-- editorconfig-checker-disable-file
{-# LANGUAGE GADTs #-}



module SystemF where

-------------------------------
-- (Types of) System F Omega --
-------------------------------

-- general recursion is introduced via a constant fix :: (k -> k) -> k

type VarName = String

data Type where
  TyVar :: VarName -> Type
  TyFun :: Type -> Type -> Type
  TyAll :: VarName -> Type -> Type
  TyAbs :: VarName -> Type -> Type
  TyApp :: Type -> Type -> Type
  TyFix :: Type -> Type
  TyMu  :: VarName -> Type -> Type

instance Show Type where
  show (TyVar x)     = x
  show (TyFun t1 t2) = "(" ++ (show t1) ++ " -> " ++ (show t2) ++ ")"
  show (TyAll x t)   = "(" ++ "all " ++ x ++ "." ++ (show t) ++ ")"
  show (TyAbs x t)   = "(" ++ "lam " ++ x ++ "." ++ (show t) ++ ")"
  show (TyApp t1 t2) = "(" ++ (show t1) ++ " " ++ (show t2) ++ ")"
  show (TyFix t)     = "(" ++ "fix " ++ (show t) ++ ")"
  show (TyMu  x t)   = "(" ++ "mu "  ++ x ++ "." ++ (show t) ++ ")"

data Kind where
  Star  :: Kind
  Arrow :: Kind -> Kind -> Kind
  deriving stock (Eq)

instance Show Kind where
  show Star          = "*"
  show (Arrow k1 k2) = "(" ++ (show k1) ++ " -> " ++ (show k2) ++ ")"

data Binding where
  TermBind :: VarName -> Type -> Binding
  TypeBind :: VarName -> Kind -> Binding

instance Show Binding where
  show (TermBind x t) = x ++ ":" ++ (show t)
  show (TypeBind x k) = x ++ "::" ++ (show k)

type Context = [Binding]

addBinding :: Context -> Binding -> Context
addBinding ctx b = b:ctx

getBinding :: Context -> VarName -> Either Type Kind
getBinding [] x = error ("variable " ++ x ++ " isn't bound in the current context")
getBinding (b:bs) x = case b of
                        (TermBind y t) -> if x == y then Left  t else getBinding bs x
                        (TypeBind y k) -> if x == y then Right k else getBinding bs x

--------------------
-- Kind Inference --
--------------------
{-
kind :: Context -> Type -> Kind
kind ctx (TyVar x) = case getBinding ctx x of
                       (Left  t) -> error ("The type variable " ++ x ++ " is assigned type " ++ (show t) ++
                                           " in the context, but it may only be bound to a kind")
                       (Right k) -> k
kind ctx (TyAbs x k1 t) = let ctx' = addBinding ctx (TypeBind x k1)
                              k2   = kind ctx' t in
                            (Arrow k1 k2)
kind ctx (TyApp t1 t2) = let k1 = kind ctx t1
                             k2 = kind ctx t2 in
                           case k1 of
                             (Arrow a b) -> if a == k2
                                              then b
                                              else error ("can't apply type " ++ (show t1) ++ " to type " ++ (show t2) ++
                                                          " since " ++ (show t1) ++ " has kind " ++ (show k1) ++ " and " ++
                                                           (show t2) ++ " has kind " ++ (show k2))
                             Star -> error ("can't apply type " ++ (show t1) ++ " to type " ++ (show t2) ++
                                            " since " ++ (show t1) ++ " has kind " ++ (show Star))
kind ctx (TyFun t1 t2) = let k1 = kind ctx t1
                             k2 = kind ctx t2 in
                           if k1 == Star && k2 == Star
                             then Star
                             else error ("for " ++ (show (TyFun t1 t2)) ++ " to be a function type, both " ++ (show t1) ++
                                         " and " ++ (show t2) ++ " must have kind " ++ (show Star))
kind ctx (TyAll x k t) = let ctx' = addBinding ctx (TypeBind x k)
                             kt   = kind ctx' t in
                           if kt == Star
                             then Star
                             else error ("if " ++ x ++ " has kind " ++ (show k) ++ " then " ++ (show t) ++ " has kind " ++
                                         (show kt) ++ ", but must have kind " ++ (show Star) ++
                                         " to be universally quantified")
kind ctx (TyFix t) = let k = kind ctx t in
                       case k of
                         (Arrow k1 k2) -> if k1 == k2 then k1 else (error "can only fix types of kind k -> k")
                         Star          -> error "cannot fix types of kind *"


-}
------------------------
-- Type Normalization --
------------------------

reduce :: Type -> Type
reduce (TyVar x) = TyVar x
reduce (TyFun t1 t2) = TyFun (reduce t1) (reduce t2)
reduce (TyAll x t) = TyAll x t
reduce (TyAbs x t) = TyAbs x t
reduce (TyFix t) = TyFix (reduce t)
reduce (TyApp t1 t2) = case t1 of
                        (TyAbs x t) -> sub t2 x t
                        _           -> (TyApp (reduce t1) t2)

-- sub a x t is t[a/x].
sub :: Type -> VarName -> Type -> Type
sub = subExcept []
  where
  subExcept :: [VarName] -> Type -> VarName -> Type -> Type
  subExcept bound t x t' = if x `elem` bound then t' else
                             case t' of
                               (TyVar y)     -> if x == y then t else (TyVar y)
                               (TyFun t1 t2) -> TyFun (subExcept bound t x t1) (subExcept bound t x t2)
                               (TyAll x' t') -> TyAll x' (subExcept (x:bound) t x t')
                               (TyAbs x' t') -> TyAbs x' (subExcept (x:bound) t x t')
                               (TyFix t')    -> TyFix (subExcept (bound) t x t')
                               (TyApp t1 t2) -> TyApp (subExcept bound t x t1) (subExcept bound t x t2)


