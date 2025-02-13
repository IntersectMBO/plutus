{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusIR.Core.Type
  ( TyName (..)
  , Name (..)
  , VarDecl (..)
  , TyVarDecl (..)
  , varDeclNameString
  , tyVarDeclNameString
  , Kind (..)
  , Type (..)
  , Datatype (..)
  , datatypeNameString
  , Recursivity (..)
  , Strictness (..)
  , Binding (..)
  , Term (..)
  , Program (..)
  , Version (..)
  , applyProgram
  , termAnn
  , bindingAnn
  , mapName
  , mapTyName
  , mapUni
  , progAnn
  , progVer
  , progTerm
  ) where

import PlutusCore (Kind, Name, TyName, Type (..), Version (..))
import PlutusCore qualified as PLC
import PlutusCore.Builtin (HasConstant (..), throwNotAConstant)
import PlutusCore.Core (UniOf)
import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Flat ()
import PlutusCore.MkPlc (Def (..), TermLike (..), TyVarDecl (..), VarDecl (..))
import PlutusCore.Name.Unique qualified as PLC
import PlutusPrelude

import Universe

import Control.Lens.TH
import Control.Monad.Except
import Data.Hashable
import Data.Text qualified as T
import Data.Word
import PlutusCore.Error (ApplyProgramError (MkApplyProgramError))

-- Datatypes

data Datatype tyname name uni a
  = Datatype a (TyVarDecl tyname a) [TyVarDecl tyname a] name [VarDecl tyname name uni a]
  deriving stock (Functor, Show, Generic)

varDeclNameString :: VarDecl tyname Name uni a -> String
varDeclNameString = T.unpack . PLC._nameText . _varDeclName

tyVarDeclNameString :: TyVarDecl TyName a -> String
tyVarDeclNameString = T.unpack . PLC._nameText . PLC.unTyName . _tyVarDeclName

datatypeNameString :: Datatype TyName name uni a -> String
datatypeNameString (Datatype _ tn _ _ _) = tyVarDeclNameString tn

-- Bindings

{- | Each multi-let-group has to be marked with its scoping:
* 'NonRec': the identifiers introduced by this multi-let are only linearly-scoped,
  i.e. an identifier cannot refer to itself or later-introduced identifiers of the group.
* 'Rec': an identifiers introduced by this multi-let group can use all other multi-lets
  of the same group (including itself), thus permitting (mutual) recursion.
-}
data Recursivity = NonRec | Rec
  deriving stock (Show, Eq, Generic, Ord)
  deriving anyclass (Hashable)

{- | Recursivity can form a 'Semigroup' / lattice, where 'NonRec' < 'Rec'.
The lattice is ordered by "power": a non-recursive binding group can be made recursive
and it will still work, but not vice versa.
The semigroup operation is the "join" of the lattice.
-}
instance Semigroup Recursivity where
  NonRec <> x = x
  Rec <> _    = Rec

data Strictness = NonStrict | Strict
  deriving stock (Show, Eq, Generic)

data Binding tyname name uni fun a
  = TermBind a Strictness (VarDecl tyname name uni a) (Term tyname name uni fun a)
  | TypeBind a (TyVarDecl tyname a) (Type tyname uni a)
  | DatatypeBind a (Datatype tyname name uni a)
  deriving stock (Functor, Generic)

deriving stock instance
  ( Show tyname
  , Show name
  , Show fun
  , Show a
  , GShow uni
  , Everywhere uni Show
  , Closed uni
  )
  => Show (Binding tyname name uni fun a)

-- Terms

{- Note [PIR as a PLC extension]
PIR is designed to be an extension of PLC, which means that we try and be strict superset of it.

The main benefit of this is simplicity, but we hope that in future it will make sharing of
theoretical and practical material easier. In the long run it would be nice if PIR was a "true"
extension of PLC (perhaps in the sense of "Trees that Grow"), and then we could potentially
even share most of the typechecker.
-}

{- Note [Declarations in Plutus Core]
In Plutus Core declarations are usually *flattened*, i.e. `(lam x ty t)`, whereas
in Plutus IR they are *reified*, i.e. `(termBind (vardecl x ty) t)`.

Plutus IR needs reified declarations to make it easier to parse *lists* of declarations,
which occur in a few places.

However, we also include all of Plutus Core's term syntax in our term syntax (and we also use
its types). We therefore have somewhat inconsistent syntax since declarations in Plutus
Core terms will be flattened. This makes the embedding obvious and makes life easier
if we were ever to use the Plutus Core AST "for real".

It would be nice to resolve the inconsistency, but this would probably require changing
Plutus Core to use reified declarations.
-}

-- See Note [PIR as a PLC extension]
data Term tyname name uni fun a
  = -- Plutus Core (ish) forms, see Note [Declarations in Plutus Core]
    Let a Recursivity (NonEmpty (Binding tyname name uni fun a)) (Term tyname name uni fun a)
  | Var a name
  | TyAbs a tyname (Kind a) (Term tyname name uni fun a)
  | LamAbs a name (Type tyname uni a) (Term tyname name uni fun a)
  | Apply a (Term tyname name uni fun a) (Term tyname name uni fun a)
  | Constant a (PLC.Some (PLC.ValueOf uni))
  | Builtin a fun
  | TyInst a (Term tyname name uni fun a) (Type tyname uni a)
  | Error a (Type tyname uni a)
  | IWrap a (Type tyname uni a) (Type tyname uni a) (Term tyname name uni fun a)
  | Unwrap a (Term tyname name uni fun a)
  | -- See Note [Constr tag type]
    Constr a (Type tyname uni a) Word64 [Term tyname name uni fun a]
  | Case a (Type tyname uni a) (Term tyname name uni fun a) [Term tyname name uni fun a]
  deriving stock (Functor, Generic)

deriving stock instance
  ( Show tyname
  , Show name
  , GShow uni
  , Everywhere uni Show
  , Show fun
  , Show a
  , Closed uni
  )
  => Show (Term tyname name uni fun a)

-- See Note [ExMemoryUsage instances for non-constants].
instance ExMemoryUsage (Term tyname name uni fun ann) where
  memoryUsage =
    Prelude.error "Internal error: 'memoryUsage' for IR 'Term' is not supposed to be forced"

type instance UniOf (Term tyname name uni fun ann) = uni

instance HasConstant (Term tyname name uni fun ()) where
  asConstant (Constant _ val) = pure val
  asConstant _                = throwNotAConstant

  fromConstant = Constant ()

instance TermLike (Term tyname name uni fun) tyname name uni fun where
  var = Var
  tyAbs = TyAbs
  lamAbs = LamAbs
  apply = Apply
  constant = Constant
  builtin = Builtin
  tyInst = TyInst
  unwrap = Unwrap
  iWrap = IWrap
  error = Error
  constr = Constr
  kase = Case

  termLet x (Def vd bind) = Let x NonRec (pure $ TermBind x Strict vd bind)
  typeLet x (Def vd bind) = Let x NonRec (pure $ TypeBind x vd bind)

data Program tyname name uni fun ann = Program
  { _progAnn  :: ann
  , _progVer  :: Version
  -- ^ The version of the program. This corresponds to the underlying Plutus Core version.
  , _progTerm :: Term tyname name uni fun ann
  }
  deriving stock (Functor, Generic)
makeLenses ''Program

deriving stock instance
  ( Show tyname
  , Show name
  , GShow uni
  , Everywhere uni Show
  , Show fun
  , Show ann
  , Closed uni
  )
  => Show (Program tyname name uni fun ann)

type instance
  PLC.HasUniques (Term tyname name uni fun ann) =
    (PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique)

type instance
  PLC.HasUniques (Program tyname name uni fun ann) =
    PLC.HasUniques (Term tyname name uni fun ann)

{- | Applies one program to another. Fails if the versions do not match
and tries to merge annotations.
-}
applyProgram
  :: (MonadError ApplyProgramError m, Semigroup a)
  => Program tyname name uni fun a
  -> Program tyname name uni fun a
  -> m (Program tyname name uni fun a)
applyProgram (Program a1 v1 t1) (Program a2 v2 t2)
  | v1 == v2 =
      pure $ Program (a1 <> a2) v1 (Apply (termAnn t1 <> termAnn t2) t1 t2)
applyProgram (Program _a1 v1 _t1) (Program _a2 v2 _t2) =
  throwError $ MkApplyProgramError v1 v2

termAnn :: Term tyname name uni fun a -> a
termAnn = \case
  Let a _ _ _    -> a
  Var a _        -> a
  TyAbs a _ _ _  -> a
  LamAbs a _ _ _ -> a
  Apply a _ _    -> a
  Constant a _   -> a
  Builtin a _    -> a
  TyInst a _ _   -> a
  Error a _      -> a
  IWrap a _ _ _  -> a
  Unwrap a _     -> a
  Constr a _ _ _ -> a
  Case a _ _ _   -> a

bindingAnn :: Binding tyname name uni fun a -> a
bindingAnn = \case
  TermBind a _ _ _ -> a
  TypeBind a _ _   -> a
  DatatypeBind a _ -> a

mapName
  :: forall tyname name name' uni fun ann
  .  (name -> name')
  -> Term tyname name uni fun ann
  -> Term tyname name' uni fun ann
mapName f = go where
    go :: Term tyname name uni fun ann -> Term tyname name' uni fun ann
    go (Constant ann val)        = Constant ann val
    go (Builtin ann fun)         = Builtin ann fun
    go (Var ann name)            = Var ann (f name)
    go (LamAbs ann name ty body) = LamAbs ann (f name) ty (go body)
    go (Apply ann fun arg)       = Apply ann (go fun) (go arg)
    go (TyAbs ann name k term)   = TyAbs ann name k (go term)
    go (TyInst ann term ty)      = TyInst ann (go term) ty
    go (Error ann ty)            = Error ann ty
    go (Constr ann ty i args)    = Constr ann ty i (fmap go args)
    go (Case ann ty arg cs)      = Case ann ty (go arg) (fmap go cs)
    go (Let ann rec bs t)        = Let ann rec (fmap goBinding bs) (go t)
    go (Unwrap ann term)         = Unwrap ann (go term)
    go (IWrap ann ty1 ty2 term)  = IWrap ann ty1 ty2 (go term)

    goBinding :: Binding tyname name uni fun ann -> Binding tyname name' uni fun ann
    goBinding (TermBind ann s vd t) = TermBind ann s (goVarDecl vd) (go t)
    goBinding (TypeBind ann tvd ty) = TypeBind ann tvd ty
    goBinding (DatatypeBind ann (Datatype annD tvd tvds match cs)) =
      DatatypeBind ann (Datatype annD tvd tvds (f match) (fmap goVarDecl cs))

    goVarDecl :: VarDecl tyname name uni ann -> VarDecl tyname name' uni ann
    goVarDecl (VarDecl ann name ty) = VarDecl ann (f name) ty

mapTyNameType
    :: forall tyname tyname' uni ann
    .  (tyname -> tyname')
    -> Type tyname uni ann
    -> Type tyname' uni ann
mapTyNameType f = go where
    go :: Type tyname uni ann -> Type tyname' uni ann
    go (TyVar ann name)        = TyVar ann (f name)
    go (TyFun ann ty1 ty2)     = TyFun ann (go ty1) (go ty2)
    go (TyIFix ann ty1 ty2)    = TyIFix ann (go ty1) (go ty2)
    go (TyForall ann name k t) = TyForall ann (f name) k (go t)
    go (TyBuiltin ann con)     = TyBuiltin ann (con)
    go (TyLam ann name k t)    = TyLam ann (f name) k (go t)
    go (TyApp ann t1 t2)       = TyApp ann (go t1) (go t2)
    go (TySOP ann tys)         = TySOP ann (map (map go) tys)

mapTyName
  :: forall tyname tyname' name uni fun ann
  .  (tyname -> tyname')
  -> Term tyname name uni fun ann
  -> Term tyname' name uni fun ann
mapTyName f = go where
    go :: Term tyname name uni fun ann -> Term tyname' name uni fun ann
    go (Constant ann val)        = Constant ann val
    go (Builtin ann fun)         = Builtin ann fun
    go (Var ann name)            = Var ann name
    go (LamAbs ann name ty body) = LamAbs ann name (goType ty) (go body)
    go (Apply ann fun arg)       = Apply ann (go fun) (go arg)
    go (TyAbs ann name k term)   = TyAbs ann (f name) k (go term)
    go (TyInst ann term ty)      = TyInst ann (go term) (goType ty)
    go (Error ann ty)            = Error ann (goType ty)
    go (Constr ann ty i args)    = Constr ann (goType ty) i (fmap go args)
    go (Case ann ty arg cs)      = Case ann (goType ty) (go arg) (fmap go cs)
    go (Let ann rec bs t)        = Let ann rec (fmap goBinding bs) (go t)
    go (Unwrap ann term)         = Unwrap ann (go term)
    go (IWrap ann ty1 ty2 term)  = IWrap ann (goType ty1) (goType ty2) (go term)

    goType :: Type tyname uni ann -> Type tyname' uni ann
    goType = mapTyNameType f

    goBinding :: Binding tyname name uni fun ann -> Binding tyname' name uni fun ann
    goBinding (TermBind ann s vd t) = TermBind ann s (goVarDecl vd) (go t)
    goBinding (TypeBind ann tvd ty) = TypeBind ann (goTyVarDecl tvd) (goType ty)
    goBinding (DatatypeBind ann (Datatype annD tvd tvds match cs)) =
      DatatypeBind ann
        (Datatype annD (goTyVarDecl tvd) (map goTyVarDecl tvds)
          match (fmap goVarDecl cs))

    goTyVarDecl :: TyVarDecl tyname ann -> TyVarDecl tyname' ann
    goTyVarDecl (TyVarDecl ann name k) = TyVarDecl ann (f name) k

    goVarDecl :: VarDecl tyname name uni ann -> VarDecl tyname' name uni ann
    goVarDecl (VarDecl ann name ty) = VarDecl ann name (goType ty)

mapUniType
    :: forall tyname uni uni' ann
    .  (SomeTypeIn uni -> SomeTypeIn uni')
    -> Type tyname uni ann
    -> Type tyname uni' ann
mapUniType f = go where
    go :: Type tyname uni ann -> Type tyname uni' ann
    go (TyVar ann name)        = TyVar ann name
    go (TyFun ann ty1 ty2)     = TyFun ann (go ty1) (go ty2)
    go (TyIFix ann ty1 ty2)    = TyIFix ann (go ty1) (go ty2)
    go (TyForall ann name k t) = TyForall ann name k (go t)
    go (TyBuiltin ann con)     = TyBuiltin ann (f con)
    go (TyLam ann name k t)    = TyLam ann name k (go t)
    go (TyApp ann t1 t2)       = TyApp ann (go t1) (go t2)
    go (TySOP ann tys)         = TySOP ann (map (map go) tys)

mapUni
    :: forall tyname uni uni' name fun ann.
       (SomeTypeIn uni -> SomeTypeIn uni')
    -> (Some (ValueOf uni) -> Some (ValueOf uni'))
    -> Term tyname name uni fun ann
    -> Term tyname name uni' fun ann
mapUni fTy fCon = go where
    go :: Term tyname name uni fun ann -> Term tyname name uni' fun ann
    go (Constant ann val)        = Constant ann (fCon val)
    go (Builtin ann fun)         = Builtin ann fun
    go (Var ann name)            = Var ann name
    go (LamAbs ann name ty body) = LamAbs ann name (goType ty) (go body)
    go (Apply ann fun arg)       = Apply ann (go fun) (go arg)
    go (TyAbs ann name k term)   = TyAbs ann name k (go term)
    go (TyInst ann term ty)      = TyInst ann (go term) (goType ty)
    go (Error ann ty)            = Error ann (goType ty)
    go (Constr ann ty i args)    = Constr ann (goType ty) i (fmap go args)
    go (Case ann ty arg cs)      = Case ann (goType ty) (go arg) (fmap go cs)
    go (Let ann rec bs t)        = Let ann rec (fmap goBinding bs) (go t)
    go (Unwrap ann term)         = Unwrap ann (go term)
    go (IWrap ann ty1 ty2 term)  = IWrap ann (goType ty1) (goType ty2) (go term)

    goType :: Type tyname uni ann -> Type tyname uni' ann
    goType = mapUniType fTy

    goBinding :: Binding tyname name uni fun ann -> Binding tyname name uni' fun ann
    goBinding (TermBind ann s vd t) = TermBind ann s (goVarDecl vd) (go t)
    goBinding (TypeBind ann tvd ty) = TypeBind ann tvd (goType ty)
    goBinding (DatatypeBind ann (Datatype annD tvd tvds match cs)) =
      DatatypeBind ann (Datatype annD tvd tvds match (fmap goVarDecl cs))

    goVarDecl :: VarDecl tyname name uni ann -> VarDecl tyname name uni' ann
    goVarDecl (VarDecl ann name ty) = VarDecl ann name (goType ty)
