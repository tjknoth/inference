module Infer where

import Type
import Syntax

import Data.Map as Map hiding (foldr)
import Data.Set as Set hiding (foldr)
import Data.List (nub)
import Data.Monoid
import Control.Monad.Except
import Control.Monad.State

newtype TypeEnv = TypeEnv (Map.Map Var Scheme)
  deriving Monoid

extend :: TypeEnv -> (Var, Scheme) -> TypeEnv
extend (TypeEnv e) (v,s) = TypeEnv $ Map.insert v s e

newtype Unique = Unique { count :: Int }

initUnique = Unique 0

-- Inference monad
type Infer a = ExceptT TypeError (State Unique) a

runInfer :: Infer (Subst, Type) -> Either TypeError Scheme
runInfer m = case evalState (runExceptT m) initUnique of
  Left err  -> Left err
  Right sch -> Right $ closeOver sch

closeOver :: (Map.Map TVar Type, Type) -> Scheme
closeOver (sub, ty) = normalize sch
  where sch = generalize emptyTyenv (apply sub ty)

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer Type
fresh = do
  s <- get
  put s{count = count s + 1}
  return $ TVar $ TV (letters !! count s)


data TypeError
  = UnificationErr Type Type
  | InfiniteType TVar Type
  | UnboundVar String


-- Type substitutions
type Subst = Map TVar Type

nullSubst :: Subst
nullSubst = Map.empty

compose :: Subst -> Subst -> Subst
compose s1 s2 = Map.map (apply s1) s2 `Map.union` s1

class Substitutable a where
  apply :: Subst -> a -> a
  ftv :: a -> Set.Set TVar

instance Substitutable Type where
  apply _ (TCon a) = TCon a
  apply s t@(TVar v) = Map.findWithDefault t v s
  apply s (TArr t1 t2) = TArr (apply s t1) (apply s t2)

  ftv (TCon _) = Set.empty
  ftv (TVar v) = Set.singleton v
  ftv (TArr t1 t2) = Set.union (ftv t1) (ftv t2)

instance Substitutable Scheme where
  apply s (Forall vs t) =
    Forall vs $ apply s' t
      where s' = foldr Map.delete s vs
  ftv (Forall vs t) = Set.difference (ftv t) (Set.fromList vs)

instance Substitutable a => Substitutable [a] where
  apply = fmap . apply
  ftv = foldr (Set.union . ftv) Set.empty

instance Substitutable TypeEnv where
  apply s (TypeEnv e) = TypeEnv $ Map.map (apply s) e
  ftv (TypeEnv e) = ftv $ Map.elems e


-- Unification
occurs :: Substitutable a => TVar -> a -> Bool
occurs v a = Set.member v (ftv a)

unify :: Type -> Type -> Infer Subst
unify (TVar a) t = bind a t
unify t (TVar a) = bind a t
unify (TCon a) (TCon b) | a == b = return nullSubst
unify (TArr l r) (TArr l' r') = do
  s1 <- unify l l'
  s2 <- unify (apply s1 r) (apply s1 r')
  return $ compose s2 s1
unify t1 t2 = throwError $ UnificationErr t1 t2

bind :: TVar -> Type -> Infer Subst
bind a t | t == TVar a = return nullSubst
         | occurs a t  = throwError $ InfiniteType a t
         | otherwise   = return $ Map.singleton a t


-- Instantiation
instantiate :: Scheme -> Infer Type
instantiate (Forall vs t) = do
  vs' <- mapM (const fresh) vs
  let s = Map.fromList $ zip vs vs'
  return $ apply s t

generalize :: TypeEnv -> Type -> Scheme
generalize env t = Forall vs t
  where vs = Set.toList $ Set.difference (ftv t) (ftv env)


-- Typing rules
infer :: TypeEnv -> Expr -> Infer (Subst, Type)
infer env ex = case ex of
  Var x -> lookupEnv env x

  App f e -> do
    tv <- fresh
    (s1, t1) <- infer env f
    (s2, t2) <- infer (apply s1 env) e
    s3 <- unify (apply s2 t1) (TArr t2 tv)
    return (s3 `compose` s2 `compose` s1, apply s3 tv)

  Lam x e -> do
    tv <- fresh
    let env' = extend env (x, Forall [] tv)
    (s1, t1) <- infer env' e
    return (s1, apply s1 (TArr tv t1))

  Let x e1 e2 -> do
    (s1,t1) <- infer env e1
    let env' = apply s1 env
        t'   = generalize env' t1
    (s2,t2) <- infer (extend env' (x, t')) e2
    return (compose s1 s2, t2)

  If g t f -> do
    (s1,t1) <- infer env g
    (s2,t2) <- infer env t
    (s3,t3) <- infer env f
    s4 <- unify t1 typeBool
    s5 <- unify t2 t3
    return (s5 `compose` s4 `compose` s3 `compose` s2 `compose` s1, apply s5 t2)

  Fix e -> do
    (s1,t) <- infer env e
    tv <- fresh
    s2 <- unify (TArr tv tv) t
    return (s2, apply s1 tv)

  Op b e1 e2 -> do
    (s1, t1) <- infer env e1
    (s2, t2) <- infer env e2
    tv <- fresh
    s3 <- unify (TArr t1 (TArr t2 tv)) (ops ! b)
    return (s1 `compose` s2 `compose` s3, apply s3 tv)

  Lit (LInt _) -> return (nullSubst, typeInt)
  Lit (LBool _) -> return (nullSubst, typeBool)

inferPrim :: TypeEnv -> [Expr] -> Type -> Infer (Subst, Type)
inferPrim env l t = do
  tv <- fresh
  (s1, tf) <- foldM inferStep (nullSubst, id) l
  s2 <- unify (apply s1 (tf tv)) t
  return (s2 `compose` s1, apply s2 tv)
  where
  inferStep (s, tf) exp = do
    (s', t) <- infer (apply s env) exp
    return (s' `compose` s, tf . (TArr t))

inferExpr :: TypeEnv -> Expr -> Either TypeError Scheme
inferExpr env = runInfer . infer env

inferTop :: TypeEnv -> [(String, Expr)] -> Either TypeError TypeEnv
inferTop env [] = Right env
inferTop env ((name, ex):xs) = case inferExpr env ex of
  Left err -> Left err
  Right ty -> inferTop (extend env (name, ty)) xs

-- Utilities
lookupEnv :: TypeEnv -> Var -> Infer (Subst, Type)
lookupEnv (TypeEnv e) x =
  case Map.lookup x e of
    Nothing -> throwError $ UnboundVar (show x)
    Just sch ->
      do t <- instantiate sch
         return (nullSubst, t)


ops :: Map Binop Type
ops = Map.fromList
      [(Add, typeInt `TArr` typeInt `TArr` typeInt)
      ,(Mul, typeInt `TArr` typeInt `TArr` typeInt)
      ,(Sub, typeInt `TArr` typeInt `TArr` typeInt)
      ,(Eql, typeInt `TArr` typeInt `TArr` typeBool)]

emptyTyenv :: TypeEnv
emptyTyenv = TypeEnv Map.empty

typeof :: TypeEnv -> Var -> Maybe Type.Scheme
typeof (TypeEnv env) name = Map.lookup name env

normalize :: Scheme -> Scheme
normalize (Forall ts body) = Forall (fmap snd ord) (normtype body)
  where
    ord = zip (nub $ fv body) (fmap TV letters)

    fv (TVar v) = [v]
    fv (TCon s) = []
    fv (TArr t1 t2) = fv t1 ++ fv t2

    normtype (TArr t1 t2) = TArr (normtype t1) (normtype t2)
    normtype (TCon s) = TCon s
    normtype (TVar v) =
      case Prelude.lookup v ord of
        Just x -> TVar x
        Nothing -> error "Type variable not in signature"
