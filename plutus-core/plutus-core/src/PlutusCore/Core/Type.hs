-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DeriveAnyClass           #-}
{-# LANGUAGE DerivingVia              #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE UndecidableInstances     #-}

-- We rely on things from this module being lazy (e.g. the PIR generators rely on types being lazy),
-- so don't use @StrictData@ in this module.

module PlutusCore.Core.Type
    ( Kind (..)
    , toPatFuncKind
    , fromPatFuncKind
    , argsFunKind
    , Type (..)
    , splitFunTyParts
    , funTyArgs
    , funTyResultType
    , Term (..)
    , Program (..)
    , HasTermLevel
    , UniOf
    , Normalized (..)
    , TyVarDecl (..)
    , VarDecl (..)
    , TyDecl (..)
    , tyDeclVar
    , HasUniques
    , Binder (..)
    , module Export
    -- * Helper functions
    , termAnn
    , typeAnn
    , mapFun
    , tyVarDeclAnn
    , tyVarDeclName
    , tyVarDeclKind
    , varDeclAnn
    , varDeclName
    , varDeclType
    , tyDeclAnn
    , tyDeclType
    , tyDeclKind
    , progAnn
    , progVer
    , progTerm
    )
where

import PlutusPrelude

import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Name
import PlutusCore.Version as Export

import Control.Lens
import Data.Hashable
import Data.Kind qualified as GHC
import Data.List.NonEmpty qualified as NE
import Data.Word
import Instances.TH.Lift ()
import Language.Haskell.TH.Lift
import Universe

data Kind ann
    = Type ann
    | KindArrow ann (Kind ann) (Kind ann)
    deriving stock (Eq, Show, Functor, Generic, Lift)
    deriving anyclass (NFData, Hashable)

-- | The kind of a pattern functor (the first 'Type' argument of 'TyIFix') at a given kind (of the
-- second 'Type' argument of 'TyIFix'):
--
-- > toPatFuncKind k = (k -> *) -> k -> *
toPatFuncKind :: Kind () -> Kind ()
toPatFuncKind k = KindArrow () (KindArrow () k (Type ())) (KindArrow () k (Type ()))

fromPatFuncKind :: Kind () -> Maybe (Kind ())
fromPatFuncKind (KindArrow () (KindArrow () k1 (Type ())) (KindArrow () k2 (Type ())))
    | k1 == k2 = Just k1
fromPatFuncKind _ = Nothing

-- | Extract all @a_i@ from @a_0 -> a_1 -> ... -> r@.
argsFunKind :: Kind ann -> [Kind ann]
argsFunKind Type{}            = []
argsFunKind (KindArrow _ k l) = k : argsFunKind l

-- | A 'Type' assigned to expressions.
type Type :: GHC.Type -> (GHC.Type -> GHC.Type) -> GHC.Type -> GHC.Type
data Type tyname uni ann
    = TyVar ann tyname -- ^ Type variable
    | TyFun ann (Type tyname uni ann) (Type tyname uni ann) -- ^ Function type
    | TyIFix ann (Type tyname uni ann) (Type tyname uni ann)
      -- ^ Fix-point type, for constructing self-recursive types
    | TyForall ann tyname (Kind ann) (Type tyname uni ann) -- ^ Polymorphic type
    | TyBuiltin ann (SomeTypeIn uni) -- ^ Builtin type
    | TyLam ann tyname (Kind ann) (Type tyname uni ann) -- ^ Type lambda
    | TyApp ann (Type tyname uni ann) (Type tyname uni ann) -- ^ Type application
    | TySOP ann [[Type tyname uni ann]] -- ^ Sum-of-products type
    deriving stock (Show, Functor, Generic)
    deriving anyclass (NFData)

-- | Get recursively all the domains and codomains of a type.
-- @splitFunTyParts (A->B->C) = [A, B, C]@
-- @splitFunTyParts (X) = [X]@
splitFunTyParts :: Type tyname uni a -> NE.NonEmpty (Type tyname uni a)
splitFunTyParts = \case
    TyFun _ t1 t2 -> t1 NE.<| splitFunTyParts t2
    t             -> pure t

-- | Get the argument types of a function type.
-- @funTyArgs (A->B->C) = [A, B]@
funTyArgs :: Type tyname uni a ->  [Type tyname uni a]
funTyArgs = NE.init . splitFunTyParts

-- | Get the result type of a function.
-- If not a function, then is the same as `id`
-- @funResultType (A->B->C) = C@
-- @funResultType (X) = X@
funTyResultType :: Type tyname uni a ->  Type tyname uni a
funTyResultType = NE.last . splitFunTyParts

data Term tyname name uni fun ann
    = Var ann name -- ^ a named variable
    | LamAbs ann name (Type tyname uni ann) (Term tyname name uni fun ann) -- ^ lambda abstraction
    | Apply ann (Term tyname name uni fun ann) (Term tyname name uni fun ann) -- ^ application
    | TyAbs ann tyname (Kind ann) (Term tyname name uni fun ann) -- ^ type abstraction
    | TyInst ann (Term tyname name uni fun ann) (Type tyname uni ann) -- ^ instantiation
    | IWrap ann (Type tyname uni ann) (Type tyname uni ann) (Term tyname name uni fun ann) -- ^ wrapping
    | Unwrap ann (Term tyname name uni fun ann) -- ^ unwrapping
    -- See Note [Constr tag type]
    | Constr ann (Type tyname uni ann) Word64 [Term tyname name uni fun ann] -- ^ constructor
    | Case ann (Type tyname uni ann) (Term tyname name uni fun ann) [Term tyname name uni fun ann] -- ^ case
    | Constant ann (Some (ValueOf uni)) -- ^ constants
    | Builtin ann fun -- ^ builtin functions
    | Error ann (Type tyname uni ann) -- ^ fail with error
    deriving stock (Functor, Generic)

deriving stock instance (Show tyname, Show name, GShow uni, Everywhere uni Show, Show fun, Show ann, Closed uni)
    => Show (Term tyname name uni fun ann)

deriving anyclass instance (NFData tyname, NFData name, NFData fun, NFData ann, Everywhere uni NFData, Closed uni)
    => NFData (Term tyname name uni fun ann)

-- See Note [ExMemoryUsage instances for non-constants].
instance ExMemoryUsage (Term tyname name uni fun ann) where
    memoryUsage = error "Internal error: 'memoryUsage' for Core 'Term' is not supposed to be forced"

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core language.
data Program tyname name uni fun ann = Program
    { _progAnn  :: ann
    , _progVer  :: Version
    , _progTerm :: Term tyname name uni fun ann
    }
    deriving stock (Functor, Generic)

makeLenses ''Program

deriving stock instance (Show tyname, Show name, GShow uni, Everywhere uni Show, Show fun, Show ann, Closed uni)
    => Show (Program tyname name uni fun ann)

deriving anyclass instance (NFData tyname, NFData name, Everywhere uni NFData, NFData fun, NFData ann, Closed uni)
    => NFData (Program tyname name uni fun ann)

-- | Specifies that the given type is a built-in one and its values can be embedded into a 'Term'.
type HasTermLevel :: forall a. (GHC.Type -> GHC.Type) -> a -> GHC.Constraint
type HasTermLevel uni = Includes uni

-- | Extract the universe from a type.
type family UniOf a :: GHC.Type -> GHC.Type

type instance UniOf (Term tyname name uni fun ann) = uni

-- | A "type variable declaration", i.e. a name and a kind for a type variable.
data TyVarDecl tyname ann = TyVarDecl
    { _tyVarDeclAnn  :: ann
    , _tyVarDeclName :: tyname
    , _tyVarDeclKind :: Kind ann
    } deriving stock (Functor, Show, Generic)
makeLenses ''TyVarDecl

-- | A "variable declaration", i.e. a name and a type for a variable.
data VarDecl tyname name uni ann = VarDecl
    { _varDeclAnn  :: ann
    , _varDeclName :: name
    , _varDeclType :: Type tyname uni ann
    } deriving stock (Functor, Show, Generic)
makeLenses ''VarDecl

-- | A "type declaration", i.e. a kind for a type.
data TyDecl tyname uni ann = TyDecl
    { _tyDeclAnn  :: ann
    , _tyDeclType :: Type tyname uni ann
    , _tyDeclKind :: Kind ann
    } deriving stock (Functor, Show, Generic)
makeLenses ''TyDecl

tyDeclVar :: TyVarDecl tyname ann -> TyDecl tyname uni ann
tyDeclVar (TyVarDecl ann name kind) = TyDecl ann (TyVar ann name) kind

instance HasUnique tyname TypeUnique => HasUnique (TyVarDecl tyname ann) TypeUnique where
    unique f (TyVarDecl ann tyname kind) =
        unique f tyname <&> \tyname' -> TyVarDecl ann tyname' kind

instance HasUnique name TermUnique => HasUnique (VarDecl tyname name uni ann) TermUnique where
    unique f (VarDecl ann name ty) =
        unique f name <&> \name' -> VarDecl ann name' ty

newtype Normalized a = Normalized
    { unNormalized :: a
    } deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic)
      deriving newtype (NFData, Pretty, PrettyBy config)
      deriving Applicative via Identity

-- | All kinds of uniques an entity contains.
type family HasUniques a :: GHC.Constraint
type instance HasUniques (Kind ann) = ()
type instance HasUniques (Type tyname uni ann) = HasUnique tyname TypeUnique
type instance HasUniques (Term tyname name uni fun ann) =
    (HasUnique tyname TypeUnique, HasUnique name TermUnique)
type instance HasUniques (Program tyname name uni fun ann) =
    HasUniques (Term tyname name uni fun ann)

typeAnn :: Type tyname uni ann -> ann
typeAnn (TyVar ann _       ) = ann
typeAnn (TyFun ann _ _     ) = ann
typeAnn (TyIFix ann _ _    ) = ann
typeAnn (TyForall ann _ _ _) = ann
typeAnn (TyBuiltin ann _   ) = ann
typeAnn (TyLam ann _ _ _   ) = ann
typeAnn (TyApp ann _ _     ) = ann
typeAnn (TySOP ann _       ) = ann

termAnn :: Term tyname name uni fun ann -> ann
termAnn (Var ann _       ) = ann
termAnn (TyAbs ann _ _ _ ) = ann
termAnn (Apply ann _ _   ) = ann
termAnn (Constant ann _  ) = ann
termAnn (Builtin  ann _  ) = ann
termAnn (TyInst ann _ _  ) = ann
termAnn (Unwrap ann _    ) = ann
termAnn (IWrap ann _ _ _ ) = ann
termAnn (Error ann _     ) = ann
termAnn (LamAbs ann _ _ _) = ann
termAnn (Constr ann _ _ _) = ann
termAnn (Case ann _ _ _  ) = ann

-- | Map a function over the set of built-in functions.
mapFun :: (fun -> fun') -> Term tyname name uni fun ann -> Term tyname name uni fun' ann
mapFun f = go where
    go (LamAbs ann name ty body)  = LamAbs ann name ty (go body)
    go (TyAbs ann name kind body) = TyAbs ann name kind (go body)
    go (IWrap ann pat arg term)   = IWrap ann pat arg (go term)
    go (Apply ann fun arg)        = Apply ann (go fun) (go arg)
    go (Unwrap ann term)          = Unwrap ann (go term)
    go (Error ann ty)             = Error ann ty
    go (TyInst ann term ty)       = TyInst ann (go term) ty
    go (Var ann name)             = Var ann name
    go (Constant ann con)         = Constant ann con
    go (Builtin ann fun)          = Builtin ann (f fun)
    go (Constr ann ty i args)     = Constr ann ty i (map go args)
    go (Case ann ty arg cs)       = Case ann ty (go arg) (map go cs)

-- | This is a wrapper to mark the place where the binder is introduced (i.e. LamAbs/TyAbs)
-- and not where it is actually used (TyVar/Var..).
-- This marking allows us to skip the (de)serialization of binders at LamAbs/TyAbs positions
-- iff 'name' is DeBruijn-encoded (level or index). See for example the instance of  'UntypedPlutusCore.Core.Instance.Flat'
newtype Binder name = Binder { unBinder :: name }
    deriving stock (Eq, Show)
    -- using this generates faster code, see discussion at <https://input-output-rnd.slack.com/archives/C48HA39RS/p1687917638566799>
    deriving Functor via Identity

{- Note [Constr tag type]
Constructor tags are not dynamically created, they can only come from the program itself.

So we do not have to worry about e.g. overflow.

The main constraints that we have are:
1. The use of the tags in the evaluator must be fast.
2. We don't want to allow nonsensical things (e.g. negative tags)
3. We don't want the format to change unexpectedly

These are in tension. The structure we use for storing case branches is a list, which is
traditionally indexed with an 'Int' (and most of the other alternatives are the same). That
suggests using 'Int' as the tag, but 'Int' allows negative tags. A 'Word' would be more
appropriate (of fixed size to satisfy 3), but then we need to be able to index lists by
'Word's.

Well, except there's nothing that _stops_ us indexing lists by 'Word's, we just need to
write our own indexing functions. So that's what we have done.

We use 'Word64' since it's the actual machine word, so no benefit from using a smaller
one (smaller values will be serialized by flat in fewer bytes anyway).
-}
