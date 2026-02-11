-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module UntypedPlutusCore.Core.Type
  ( TPLC.UniOf
  , TPLC.Version (..)
  , TPLC.Binder (..)
  , Term (..)
  , Program (..)
  , progAnn
  , progVer
  , progTerm
  , bindFunM
  , bindFun
  , mapFun
  , termAnn
  , modifyTermAnn
  , UVarDecl (..)
  , uvarDeclName
  , uvarDeclAnn
  ) where

import Control.Lens
import Control.Monad.Except
import PlutusPrelude

import Data.Vector
import Data.Word
import PlutusCore.Builtin qualified as TPLC
import PlutusCore.Core qualified as TPLC
import PlutusCore.MkPlc
import PlutusCore.Name.Unique qualified as TPLC
import Universe

{- Note [Term constructor ordering and numbers]
Ordering of constructors has a small but real effect on efficiency.
It's slightly more efficient to hit the earlier constructors, so it's better to put the more
common ones first.

The current ordering is based on their *empirically observed* frequency. We should check this
occasionally.

Additionally, the first 7 (or 3 on 32-bit systems) constructors will get *pointer tags*, which allows
more efficient access when casing on them. So we ideally want to keep the number of constructors
at 7 or fewer.

We've got 8 constructors, *but* the last one is Error, which is only going to be seen at most
once per program, so it's not too big a deal if it doesn't get a tag.

See the GHC Notes "Tagging big families" and "Double switching for big families" in
GHC.StgToCmm.Expr for more details.
-}

{- Note [Supported case-expressions]
Originally 'Case' was introduced to only work with 'Constr', which together create the
sums-of-products approach to representing data types.

However in https://github.com/IntersectMBO/plutus/issues/6602 we decided that the best way to
speed up processing values of built-in types is to extend 'Case' such that it supports pattern
matching on those.

Currently, 'Case' only supports booleans and integers, but we plan to extend it to lists and data.

See the @CaseBuiltin DefaultUni@ instance for how casing behaves for supported built-in types.
-}

{-| The type of Untyped Plutus Core terms. Mirrors the type of Typed Plutus Core terms except

1. all types are removed
2. 'IWrap' and 'Unwrap' are removed
3. type abstractions are replaced with 'Delay'
4. type instantiations are replaced with 'Force'

The latter two are due to the fact that we don't have value restriction in Typed Plutus Core
and hence a computation can be stuck expecting only a single type argument for the computation
to become unstuck. Therefore we can't just silently remove type abstractions and instantiations and
need to replace them with something else that also blocks evaluation (in order for the semantics
of an erased program to match with the semantics of the original typed one). 'Delay' and 'Force'
serve exactly this purpose. -}

-- Making all the fields strict gives us a couple of percent in benchmarks
-- See Note [Term constructor ordering and numbers]
data Term name uni fun ann
  = Var !ann !name
  | LamAbs !ann !name !(Term name uni fun ann)
  | Apply !ann !(Term name uni fun ann) !(Term name uni fun ann)
  | Force !ann !(Term name uni fun ann)
  | Delay !ann !(Term name uni fun ann)
  | Constant !ann !(Some (ValueOf uni))
  | Builtin !ann !fun
  | -- This is the cutoff at which constructors won't get pointer tags
    -- See Note [Term constructor ordering and numbers]
    Error !ann
  | -- TODO: worry about overflow, maybe use an Integer
    -- See Note [Constr tag type]
    Constr !ann !Word64 ![Term name uni fun ann]
  | -- See Note [Supported case-expressions].
    Case !ann !(Term name uni fun ann) !(Vector (Term name uni fun ann))
  deriving stock (Functor, Generic)

deriving stock instance
  (Show name, GShow uni, Everywhere uni Show, Show fun, Show ann, Closed uni)
  => Show (Term name uni fun ann)

deriving anyclass instance
  (NFData name, NFData fun, NFData ann, Everywhere uni NFData, Closed uni)
  => NFData (Term name uni fun ann)

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core language.
data Program name uni fun ann = Program
  { _progAnn :: ann
  , _progVer :: TPLC.Version
  , _progTerm :: Term name uni fun ann
  }
  deriving stock (Functor, Generic)

makeLenses ''Program

deriving stock instance
  (Show name, GShow uni, Everywhere uni Show, Show fun, Show ann, Closed uni)
  => Show (Program name uni fun ann)

deriving anyclass instance
  (NFData name, Everywhere uni NFData, NFData fun, NFData ann, Closed uni)
  => NFData (Program name uni fun ann)

type instance TPLC.UniOf (Term name uni fun ann) = uni

instance TermLike (Term name uni fun) TPLC.TyName name uni fun where
  var = Var
  tyAbs = \ann _ _ -> Delay ann
  lamAbs = \ann name _ -> LamAbs ann name
  apply = Apply
  constant = Constant
  builtin = Builtin
  tyInst = \ann term _ -> Force ann term
  unwrap = const id
  iWrap = \_ _ _ -> id
  error = \ann _ -> Error ann
  constr = \ann _ i es -> Constr ann i es
  kase = \ann _ arg cs -> Case ann arg (fromList cs)

instance TPLC.HasConstant (Term name uni fun ()) where
  asConstant (Constant _ val) = pure val
  asConstant _ = throwError TPLC.notAConstant

  fromConstant = Constant ()

type instance TPLC.HasUniques (Term name uni fun ann) = TPLC.HasUnique name TPLC.TermUnique
type instance TPLC.HasUniques (Program name uni fun ann) = TPLC.HasUniques (Term name uni fun ann)

-- | An untyped "variable declaration", i.e. a name for a variable.
data UVarDecl name ann = UVarDecl
  { _uvarDeclAnn :: ann
  , _uvarDeclName :: name
  }
  deriving stock (Functor, Show, Generic)

makeLenses ''UVarDecl

-- | Return the outermost annotation of a 'Term'.
termAnn :: Term name uni fun ann -> ann
termAnn (Constant ann _) = ann
termAnn (Builtin ann _) = ann
termAnn (Var ann _) = ann
termAnn (LamAbs ann _ _) = ann
termAnn (Apply ann _ _) = ann
termAnn (Delay ann _) = ann
termAnn (Force ann _) = ann
termAnn (Error ann) = ann
termAnn (Constr ann _ _) = ann
termAnn (Case ann _ _) = ann

modifyTermAnn :: (ann -> ann) -> Term name uni fun ann -> Term name uni fun ann
modifyTermAnn f = \case
  Constant ann c -> Constant (f ann) c
  Builtin ann b -> Builtin (f ann) b
  Var ann v -> Var (f ann) v
  LamAbs ann x body -> LamAbs (f ann) x body
  Apply ann fun arg -> Apply (f ann) fun arg
  Delay ann body -> Delay (f ann) body
  Force ann body -> Force (f ann) body
  Error ann -> Error (f ann)
  Constr ann i args -> Constr (f ann) i args
  Case ann scrut alts -> Case (f ann) scrut alts

bindFunM
  :: Monad m
  => (ann -> fun -> m (Term name uni fun' ann))
  -> Term name uni fun ann
  -> m (Term name uni fun' ann)
bindFunM f = go
  where
    go (Constant ann val) = pure $ Constant ann val
    go (Builtin ann fun) = f ann fun
    go (Var ann name) = pure $ Var ann name
    go (LamAbs ann name body) = LamAbs ann name <$> go body
    go (Apply ann fun arg) = Apply ann <$> go fun <*> go arg
    go (Delay ann term) = Delay ann <$> go term
    go (Force ann term) = Force ann <$> go term
    go (Error ann) = pure $ Error ann
    go (Constr ann i args) = Constr ann i <$> traverse go args
    go (Case ann arg cs) = Case ann <$> go arg <*> traverse go cs

bindFun
  :: (ann -> fun -> Term name uni fun' ann)
  -> Term name uni fun ann
  -> Term name uni fun' ann
bindFun f = runIdentity . bindFunM (coerce f)

mapFun :: (ann -> fun -> fun') -> Term name uni fun ann -> Term name uni fun' ann
mapFun f = bindFun $ \ann fun -> Builtin ann (f ann fun)
