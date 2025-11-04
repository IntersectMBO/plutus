{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
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
  , progAnn
  , progVer
  , progTerm
  ) where

import PlutusCore (Kind, Name, TyName, Type (..), Version (..))
import PlutusCore qualified as PLC
import PlutusCore.Builtin (HasConstant (..), notAConstant)
import PlutusCore.Core (UniOf)
import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.FlatInstances ()
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
  asConstant _                = throwError notAConstant

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
