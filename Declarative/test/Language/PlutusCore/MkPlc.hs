
module Language.PlutusCore.MkPlc ( VarDecl (..)
                                 , TyVarDecl (..)
                                 , TyDecl (..)
                                 , mkVar
                                 , mkTyVar
                                 , tyDeclVar
                                 , Def (..)
                                 , TermDef
                                 , TypeDef
                                 , FunctionType (..)
                                 , FunctionDef (..)
                                 , functionTypeToType
                                 , functionDefToType
                                 , functionDefVarDecl
                                 , mkFunctionDef
                                 , mkTermLet
                                 , mkTypeLet
                                 , mkIterTyForall
                                 , mkIterTyLam
                                 , mkIterApp
                                 , mkIterTyFun
                                 , mkIterLamAbs
                                 , mkIterInst
                                 , mkIterTyAbs
                                 , mkIterTyApp
                                 , mkIterKindArrow
                                 ) where

import           Language.PlutusCore.Type

import           Data.List                (foldl')
import           GHC.Generics             (Generic)

-- | A "variable declaration", i.e. a name and a type for a variable.
data VarDecl tyname name a = VarDecl {varDeclAnn::a, varDeclName::name a, varDeclType::Type tyname a}
    deriving (Functor, Show, Eq, Generic)

-- | Make a 'Var' referencing the given 'VarDecl'.
mkVar :: a -> VarDecl tyname name a -> Term tyname name a
mkVar x = Var x . varDeclName

-- | A "type variable declaration", i.e. a name and a kind for a type variable.
data TyVarDecl tyname a = TyVarDecl {tyVarDeclAnn::a, tyVarDeclName::tyname a, tyVarDeclKind::Kind a}
    deriving (Functor, Show, Eq, Generic)

-- | Make a 'TyVar' referencing the given 'TyVarDecl'.
mkTyVar :: a -> TyVarDecl tyname a -> Type tyname a
mkTyVar x = TyVar x . tyVarDeclName

-- | A "type declaration", i.e. a kind for a type.
data TyDecl tyname a = TyDecl {tyDeclAnn::a, tyDeclType::Type tyname a, tyDeclKind::Kind a}
    deriving (Functor, Show, Eq, Generic)

tyDeclVar :: TyVarDecl tyname a -> TyDecl tyname a
tyDeclVar (TyVarDecl ann name kind) = TyDecl ann (TyVar ann name) kind

-- | A definition. Pretty much just a pair with more descriptive names.
data Def var val = Def { defVar::var, defVal::val} deriving (Show, Eq, Ord, Generic)

-- | A term definition as a variable.
type TermDef tyname name a = Def (VarDecl tyname name a) (Term tyname name a)
-- | A type definition as a type variable.
type TypeDef tyname a = Def (TyVarDecl tyname a) (Type tyname a)

-- | The type of a PLC function.
data FunctionType tyname ann = FunctionType
    { _functionTypeAnn :: ann              -- ^ An annotation.
    , _functionTypeDom :: Type tyname ann  -- ^ The domain of a function.
    , _functionTypeCod :: Type tyname ann  -- ^ The codomain of the function.
    }

-- Should we parameterize 'VarDecl' by @ty@ rather than @tyname@, so that we can define
-- 'FunctionDef' as 'TermDef FunctionType tyname name ann'?
-- Perhaps we even should define general 'Decl' and 'Def' that cover all of the cases?
-- | A PLC function.
data FunctionDef tyname name ann = FunctionDef
    { _functionDefAnn  :: ann                      -- ^ An annotation.
    , _functionDefName :: name ann                 -- ^ The name of a function.
    , _functionDefType :: FunctionType tyname ann  -- ^ The type of the function.
    , _functionDefTerm :: Term tyname name ann     -- ^ The definition of the function.
    }

-- | Convert a 'FunctionType' to the corresponding 'Type'.
functionTypeToType :: FunctionType tyname ann -> Type tyname ann
functionTypeToType (FunctionType ann dom cod) = TyFun ann dom cod

-- | Get the type of a 'FunctionDef'.
functionDefToType :: FunctionDef tyname name ann -> Type tyname ann
functionDefToType (FunctionDef _ _ funTy _) = functionTypeToType funTy

-- | Convert a 'FunctionDef' to a 'VarDecl'. I.e. ignore the actual term.
functionDefVarDecl :: FunctionDef tyname name ann -> VarDecl tyname name ann
functionDefVarDecl (FunctionDef ann name funTy _) = VarDecl ann name $ functionTypeToType funTy

-- | Make a 'FunctioDef'. Return 'Nothing' if the provided type is not functional.
mkFunctionDef
    :: ann
    -> name ann
    -> Type tyname ann
    -> Term tyname name ann
    -> Maybe (FunctionDef tyname name ann)
mkFunctionDef annName name (TyFun annTy dom cod) term =
    Just $ FunctionDef annName name (FunctionType annTy dom cod) term
mkFunctionDef _       _    _                     _    = Nothing

-- | Make a "let-binding" for a term.
mkTermLet
    :: a
    -> TermDef tyname name a
    -> Term tyname name a -- ^ The body of the let, possibly referencing the name.
    -> Term tyname name a
mkTermLet x1 (Def (VarDecl x2 name ty) bind) body = Apply x1 (LamAbs x2 name ty body) bind

-- | Make a "let-binding" for a type. Note: the body must be a value.
mkTypeLet
    :: a
    -> TypeDef tyname a
    -> Term tyname name a -- ^ The body of the let, possibly referencing the name.
    -> Term tyname name a
mkTypeLet x1 (Def (TyVarDecl x2 name k) bind) body = TyInst x1 (TyAbs x2 name k body) bind

-- | Make an iterated application.
mkIterApp
    :: a
    -> Term tyname name a -- ^ @f@
    -> [Term tyname name a] -- ^@[ x0 ... xn ]@
    -> Term tyname name a -- ^ @[f x0 ... xn ]@
mkIterApp x = foldl' (Apply x)

-- | Make an iterated instantiation.
mkIterInst
    :: a
    -> Term tyname name a -- ^ @a@
    -> [Type tyname a] -- ^ @ [ x0 ... xn ] @
    -> Term tyname name a -- ^ @{ a x0 ... xn }@
mkIterInst x = foldl' (TyInst x)

-- | Lambda abstract a list of names.
mkIterLamAbs
    :: [VarDecl tyname name a]
    -> Term tyname name a
    -> Term tyname name a
mkIterLamAbs args body = foldr (\(VarDecl x n ty) acc -> LamAbs x n ty acc) body args

-- | Type abstract a list of names.
mkIterTyAbs
    :: [TyVarDecl tyname a]
    -> Term tyname name a
    -> Term tyname name a
mkIterTyAbs args body = foldr (\(TyVarDecl x n k) acc -> TyAbs x n k acc) body args

-- | Make an iterated type application.
mkIterTyApp
    :: a
    -> Type tyname a -- ^ @f@
    -> [Type tyname a] -- ^ @[ x0 ... xn ]@
    -> Type tyname a -- ^ @[ f x0 ... xn ]@
mkIterTyApp x = foldl' (TyApp x)

-- | Make an iterated function type.
mkIterTyFun
    :: a
    -> [Type tyname a]
    -> Type tyname a
    -> Type tyname a
mkIterTyFun x tys target = foldr (\ty acc -> TyFun x ty acc) target tys

-- | Universally quantify a list of names.
mkIterTyForall
    :: [TyVarDecl tyname a]
    -> Type tyname a
    -> Type tyname a
mkIterTyForall args body = foldr (\(TyVarDecl x n k) acc -> TyForall x n k acc) body args

-- | Lambda abstract a list of names.
mkIterTyLam
    :: [TyVarDecl tyname a]
    -> Type tyname a
    -> Type tyname a
mkIterTyLam args body = foldr (\(TyVarDecl x n k) acc -> TyLam x n k acc) body args

-- | Make an iterated function kind.
mkIterKindArrow
    :: a
    -> [Kind a]
    -> Kind a
    -> Kind a
mkIterKindArrow x kinds target = foldr (KindArrow x) target kinds
