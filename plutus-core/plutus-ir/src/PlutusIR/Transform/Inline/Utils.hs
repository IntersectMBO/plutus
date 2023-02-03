{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeFamilies     #-}

{- | Types and their functions, and general utility (including heuristics) for inlining. -}

module PlutusIR.Transform.Inline.Utils where

import PlutusIR
import PlutusIR.Analysis.Dependencies qualified as Deps
import PlutusIR.Analysis.Usages qualified as Usages
import PlutusIR.Purity (firstEffectfulTerm, isPure)
import PlutusIR.Transform.Rename ()
import PlutusPrelude

import PlutusCore.Annotation
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Name
import PlutusCore.Quote
import PlutusCore.Rename

import Control.Lens hiding (Strict)
import Control.Monad.Reader
import Control.Monad.State

import Data.Map qualified as Map
import Data.Semigroup.Generic (GenericSemigroupMonoid (..))

-- | Substitution range, 'SubstRng' in the paper but no 'Susp' case.
-- See Note [Inlining approach and 'Secrets of the GHC Inliner']
newtype InlineTerm tyname name uni fun a =
    Done (Dupable (Term tyname name uni fun a)) --out expressions

-- | Term substitution, 'Subst' in the paper.
-- A map of unprocessed variable and its substitution range.
newtype TermEnv tyname name uni fun a =
    TermEnv { _unTermEnv :: UniqueMap TermUnique (InlineTerm tyname name uni fun a) }
    deriving newtype (Semigroup, Monoid)

-- | Type substitution, similar to `TermEnv` but for types.
-- A map of unprocessed type variable and its substitution range.
newtype TypeEnv tyname uni a =
    TypeEnv { _unTypeEnv :: UniqueMap TypeUnique (Dupable (Type tyname uni a)) }
    deriving newtype (Semigroup, Monoid)

-- | Substitution for both terms and types.
-- Similar to 'Subst' in the paper, but the paper only has terms.
data Subst tyname name uni fun a = Subst { _termEnv :: TermEnv tyname name uni fun a
                                         , _typeEnv :: TypeEnv tyname uni a
                                         }
    deriving stock (Generic)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid (Subst tyname name uni fun a))

makeLenses ''TermEnv
makeLenses ''TypeEnv
makeLenses ''Subst

-- | Look up the unprocessed variable in the substitution.
lookupTerm
    :: (HasUnique name TermUnique)
    => name -- ^ The name of the variable.
    -> Subst tyname name uni fun a -- ^ The substitution.
    -> Maybe (InlineTerm tyname name uni fun a)
lookupTerm n subst = lookupName n $ subst ^. termEnv . unTermEnv

-- | Insert the unprocessed variable into the substitution.
extendTerm
    :: (HasUnique name TermUnique)
    => name -- ^ The name of the variable.
    -> InlineTerm tyname name uni fun a -- ^ The substitution range.
    -> Subst tyname name uni fun a -- ^ The substitution.
    -> Subst tyname name uni fun a
extendTerm n clos subst = subst & termEnv . unTermEnv %~ insertByName n clos

-- | Look up the unprocessed type variable in the substitution.
lookupType
    :: (HasUnique tyname TypeUnique)
    => tyname
    -> Subst tyname name uni fun a
    -> Maybe (Dupable (Type tyname uni a))
lookupType tn subst = lookupName tn $ subst ^. typeEnv . unTypeEnv

-- | Check if the type substitution is empty.
isTypeSubstEmpty :: Subst tyname name uni fun a -> Bool
isTypeSubstEmpty (Subst _ (TypeEnv tyEnv)) = isEmpty tyEnv

-- | Insert the unprocessed type variable into the substitution.
extendType
    :: (HasUnique tyname TypeUnique)
    => tyname -- ^ The name of the type variable.
    -> Type tyname uni a -- ^ Its type.
    -> Subst tyname name uni fun a -- ^ The substitution.
    -> Subst tyname name uni fun a
extendType tn ty subst = subst &  typeEnv . unTypeEnv %~ insertByName tn (dupable ty)


type ExternalConstraints tyname name uni fun m =
    ( HasUnique name TermUnique
    , HasUnique tyname TypeUnique
    , Eq name
    , PLC.ToBuiltinMeaning uni fun
    , MonadQuote m
    )

type InliningConstraints tyname name uni fun =
    ( HasUnique name TermUnique
    , HasUnique tyname TypeUnique
    , Eq name
    , PLC.ToBuiltinMeaning uni fun
    )

data InlineInfo name fun a = InlineInfo
    { _iiStrictnessMap :: Deps.StrictnessMap
    -- ^ Is it strict? Only needed for PIR, not UPLC
    , _iiUsages        :: Usages.Usages
    -- ^ how many times is it used?
    , _iiHints         :: InlineHints name a
    -- ^ have we explicitly been told to inline.
    , _iiBuiltinVer    :: PLC.BuiltinVersion fun
    -- ^ the builtin version.
    }
makeLenses ''InlineInfo

-- Using a concrete monad makes a very large difference to the performance of this module
-- (determined from profiling)
-- | The monad the inliner runs in.
type InlineM tyname name uni fun a =
    ReaderT (InlineInfo name fun a) (StateT (Subst tyname name uni fun a) Quote)

-- | Check if term is pure. See Note [Inlining and purity]
checkPurity
    :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => Term tyname name uni fun a -> InlineM tyname name uni fun a Bool
checkPurity t = do
    strctMap <- view iiStrictnessMap
    builtinVer <- view iiBuiltinVer
    let strictnessFun n' = Map.findWithDefault NonStrict (n' ^. theUnique) strctMap
    pure $ isPure builtinVer strictnessFun t

{- Note [Inlining and purity]
When can we inline something that might have effects? We must remember that we often also
remove a binding that we inline.

For strict bindings, the answer is that we can't: we will delay the effects to the use site,
so they may happen multiple times (or none). So we can only inline bindings whose RHS is pure,
or if we can prove that the effects don't change. We take a conservative view on this,
saying that no effects change if:
- The variable is clearly the first possibly-effectful term evaluated in the body
- The variable is used exactly once (so we won't duplicate or remove effects)

For non-strict bindings, the effects already happened at the use site, so it's fine to inline it
unconditionally.
-}

nameUsedAtMostOnce :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => name
    -> InlineM tyname name uni fun a Bool
nameUsedAtMostOnce n = do
    usgs <- view iiUsages
    -- 'inlining' terms used 0 times is a cheap way to remove dead code while we're here
    pure $ Usages.getUsageCount n usgs <= 1

effectSafe :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => Term tyname name uni fun a
    -> Strictness
    -> name
    -> Bool -- ^ is it pure?
    -> InlineM tyname name uni fun a Bool
effectSafe body s n purity = do
    -- This can in the worst case traverse a lot of the term, which could lead to us
    -- doing ~quadratic work as we process the program. However in practice most term
    -- types will make it give up, so it's not too bad.
    let immediatelyEvaluated = case firstEffectfulTerm body of
            Just (Var _ n') -> n == n'
            _               -> False
    pure $ case s of
        Strict    -> purity || immediatelyEvaluated
        NonStrict -> True

-- | Should we inline? Should only inline things that won't duplicate work or code.
-- See Note [Inlining approach and 'Secrets of the GHC Inliner']
acceptable ::  Term tyname name uni fun a -> InlineM tyname name uni fun a Bool
acceptable t =
    -- See Note [Inlining criteria]
    pure $ costIsAcceptable t && sizeIsAcceptable t

{- Note [Inlining criteria]
What gets inlined? Our goals are simple:
- Make the resulting program faster (or at least no slower)
- Make the resulting program smaller (or at least no bigger)
- Inline as much as we can, since it exposes optimization opportunities

There are two easy cases:
- Inlining approximately variable-sized and variable-costing terms (e.g. builtins, other variables)
- Inlining single-use terms

After that it gets more difficult. As soon as we're inlining things that are not variable-sized
and are used more than once, we are at risk of doing more work or making things bigger.

There are a few things we could do to do this in a more principled way, such as call-site inlining
based on whether a function is fully applied.
-}

-- | Is the cost increase (in terms of evaluation work) of inlining a variable whose RHS is
-- the given term acceptable?
costIsAcceptable :: Term tyname name uni fun a -> Bool
costIsAcceptable = \case
  Builtin{}  -> True
  Var{}      -> True
  Constant{} -> True
  Error{}    -> True
  -- This will mean that we create closures at each use site instead of
  -- once, but that's a very low cost which we're okay rounding to 0.
  LamAbs{}   -> True
  TyAbs{}    -> True

  -- Arguably we could allow these two, but they're uncommon anyway
  IWrap{}    -> False
  Unwrap{}   -> False

  Apply{}    -> False
  TyInst{}   -> False
  Let{}      -> False

-- | Is the size increase (in the AST) of inlining a variable whose RHS is
-- the given term acceptable?
sizeIsAcceptable :: Term tyname name uni fun a -> Bool
sizeIsAcceptable = \case
  Builtin{}  -> True
  Var{}      -> True
  Error{}    -> True
  LamAbs {}  -> False
  TyAbs {}   -> False

  -- Arguably we could allow these two, but they're uncommon anyway
  IWrap{}    -> False
  Unwrap{}   -> False
  -- Constants can be big! We could check the size here and inline if they're
  -- small, but probably not worth it
  Constant{} -> False
  Apply{}    -> False
  TyInst{}   -> False
  Let{}      -> False

-- | Is this a an utterly trivial type which might as well be inlined?
trivialType :: Type tyname uni a -> Bool
trivialType = \case
    TyBuiltin{} -> True
    TyVar{}     -> True
    _           -> False
