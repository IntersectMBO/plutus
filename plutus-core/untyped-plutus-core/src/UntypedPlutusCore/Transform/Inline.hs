{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE ViewPatterns     #-}
{- |
An inlining pass.

This pass is essentially a copy of the PIR inliner, and should be KEPT IN SYNC with it.
It's hard to do this with true abstraction, so we just have to keep two copies reasonably
similar.

However, there are some differences. In the interests of making it easier to keep
things in sync, these are explicitly listed in Note [Differences from PIR inliner].
If you add another difference, please note it there! Obviously fewer differences is
better.

See Note [The problem of inlining destructors].
-}
module UntypedPlutusCore.Transform.Inline (inline, InlineHints (..)) where

import PlutusPrelude
import UntypedPlutusCore.Analysis.Usages qualified as Usages
import UntypedPlutusCore.Core.Plated
import UntypedPlutusCore.Core.Type
import UntypedPlutusCore.MkUPlc
import UntypedPlutusCore.Rename ()

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.InlineUtils
import PlutusCore.Name
import PlutusCore.Quote

import Control.Lens hiding (Strict)
import Control.Monad.Reader
import Control.Monad.State

import Data.Map qualified as Map
import Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import Witherable

{- Note [Differences from PIR inliner]

1. No types (obviously).
2. No strictness information (we only have lambda arguments, which are always strict).
3. Handling of multiple beta-reductions in one go, this is handled in PIR by a dedicated pass.
4. Don't inline lambdas with small bodies. We do this in PIR but we *probably* shouldn't really. But doing it here
is actively harmful, so we don't include it.
5. Simplistic purity analysis, in particular we don't try to be clever about builtins (should mostly be handled in PIR).
-}

newtype InlineTerm name uni fun a = Done (Term name uni fun a)

newtype TermEnv name uni fun a = TermEnv { _unTermEnv :: PLC.UniqueMap TermUnique (InlineTerm name uni fun a) }
    deriving newtype (Semigroup, Monoid)

-- See Note [Differences from PIR inliner] 1
newtype Subst name uni fun a = Subst { _termEnv :: TermEnv name uni fun a }
    deriving stock (Generic)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid (Subst name uni fun a))

makeLenses ''TermEnv
makeLenses ''Subst

type ExternalConstraints name uni fun m =
    ( HasUnique name TermUnique
    , PLC.ToBuiltinMeaning uni fun
    , MonadQuote m
    )

type InliningConstraints name uni fun =
    ( HasUnique name TermUnique
    , PLC.ToBuiltinMeaning uni fun
    )

-- See Note [Differences from PIR inliner] 2
data InlineInfo name a = InlineInfo { _usages :: Usages.Usages, _hints :: InlineHints name a }

-- Using a concrete monad makes a very large difference to the performance of this module (determined from profiling)
type InlineM name uni fun a = ReaderT (InlineInfo name a) (StateT (Subst name uni fun a) Quote)

lookupTerm
    :: (HasUnique name TermUnique)
    => name
    -> Subst name uni fun a
    -> Maybe (InlineTerm name uni fun a)
lookupTerm n subst = lookupName n $ subst ^. termEnv . unTermEnv

extendTerm
    :: (HasUnique name TermUnique)
    => name
    -> InlineTerm name uni fun a
    -> Subst name uni fun a
    -> Subst name uni fun a
extendTerm n clos subst = subst & termEnv . unTermEnv %~ insertByName n clos

-- | Inline simple bindings. Relies on global uniqueness, and preserves it.
-- See Note [Inlining and global uniqueness]
inline
    :: forall name uni fun m a
    . ExternalConstraints name uni fun m
    => InlineHints name a
    -> Term name uni fun a
    -> m (Term name uni fun a)
inline hints t = let
        inlineInfo :: InlineInfo name a
        inlineInfo = InlineInfo usgs hints
        usgs :: Map.Map Unique Int
        usgs = Usages.runTermUsages t
    in liftQuote $ flip evalStateT mempty $ flip runReaderT inlineInfo $ processTerm t

-- See Note [Differences from PIR inliner] 3
{-| Extract the list of applications from a term, a bit like a "multi-beta" reduction.

Some examples will help:
[(\x . t) a] -> Just ([(x, a)], t)

[[[(\x . (\y . (\z . t))) a] b] c] -> Just ([(x, a), (y, b), (z, c)]) t)

[[(\x . t) a] b] -> Nothing
-}
extractApps :: Term name uni fun a -> Maybe ([UTermDef name uni fun a], Term name uni fun a)
extractApps = collectArgs []
  where
      collectArgs argStack (Apply _ f arg) = collectArgs (arg:argStack) f
      collectArgs argStack t               = matchArgs argStack [] t
      matchArgs (arg:rest) acc (LamAbs a n body) = matchArgs rest (Def (UVarDecl a n) arg:acc) body
      matchArgs []         acc t                 = if null acc then Nothing else Just (reverse acc, t)
      matchArgs (_:_)      _   _                 = Nothing

-- | The inverse of 'extractApps'.
restoreApps :: [UTermDef name uni fun a] -> Term name uni fun a -> Term name uni fun a
restoreApps defs t = makeLams [] t (reverse defs)
  where
      makeLams args acc (Def (UVarDecl a n) rhs:rest) = makeLams (rhs:args) (LamAbs a n acc) rest
      makeLams args acc []                            = makeApps args acc
      -- This isn't the best annotation, but it will do
      makeApps (arg:args) acc = makeApps args (Apply (termAnn acc) acc arg)
      makeApps [] acc         = acc

processTerm
    :: forall name uni fun a. InliningConstraints name uni fun
    => Term name uni fun a
    -> InlineM name uni fun a (Term name uni fun a)
processTerm = handleTerm where
    handleTerm :: Term name uni fun a -> InlineM name uni fun a (Term name uni fun a)
    handleTerm = \case
        v@(Var _ n) -> fromMaybe v <$> substName n
        -- See Note [Differences from PIR inliner] 3
        (extractApps -> Just (bs, t)) -> do
            bs' <- wither processSingleBinding bs
            t' <- processTerm t
            pure $ restoreApps bs' t'
        t -> forMOf termSubterms t processTerm

    -- See Note [Renaming strategy]
    substName :: name -> InlineM name uni fun a (Maybe (Term name uni fun a))
    substName name = gets (lookupTerm name) >>= traverse renameTerm
    -- See Note [Inlining approach and 'Secrets of the GHC Inliner']
    renameTerm :: InlineTerm name uni fun a -> InlineM name uni fun a (Term name uni fun a)
    renameTerm = \case
        -- Already processed term, just rename and put it in, don't do any
        -- further optimization here.
        Done t -> PLC.rename t

processSingleBinding :: InliningConstraints name uni fun => UTermDef name uni fun a -> InlineM name uni fun a (Maybe (UTermDef name uni fun a))
processSingleBinding (Def vd@(UVarDecl a n) rhs) = do
    rhs' <- maybeAddSubst a n rhs
    pure $ Def vd <$> rhs'

-- NOTE:  Nothing means that we are inlining the term:
--   * we have extended the substitution, and
--   * we are removing the binding (hence we return Nothing)
maybeAddSubst
    :: forall name uni fun a. InliningConstraints name uni fun
    => a
    -> name
    -> Term name uni fun a
    -> InlineM name uni fun a (Maybe (Term name uni fun a))
maybeAddSubst a n rhs = do
    rhs' <- processTerm rhs

    -- Check whether we've been told specifically to inline this
    hints <- asks _hints
    let hinted = shouldInline hints a n

    preUnconditional <- preInlineUnconditional rhs'
    if preUnconditional
    then extendAndDrop (Done rhs')
    else do
        -- See Note [Inlining approach and 'Secrets of the GHC Inliner']
        postUnconditional <- postInlineUnconditional rhs'
        if hinted || postUnconditional
        then extendAndDrop (Done rhs')
        else pure $ Just rhs'
    where
        extendAndDrop :: forall b . InlineTerm name uni fun a -> InlineM name uni fun a (Maybe b)
        extendAndDrop t = modify' (extendTerm n t) >> pure Nothing

        checkPurity :: Term name uni fun a -> InlineM name uni fun a Bool
        checkPurity t = pure $ isPure t

        preInlineUnconditional :: Term name uni fun a -> InlineM name uni fun a Bool
        preInlineUnconditional t = do
            usgs <- asks _usages
            -- 'inlining' terms used 0 times is a cheap way to remove dead code while we're here
            let termUsedAtMostOnce = Usages.getUsageCount n usgs <= 1
            -- See Note [Inlining and purity]
            termIsPure <- checkPurity t
            pure $ termUsedAtMostOnce && termIsPure

        -- | Should we inline? Should only inline things that won't duplicate work or code.
        -- See Note [Inlining approach and 'Secrets of the GHC Inliner']
        postInlineUnconditional ::  Term name uni fun a -> InlineM name uni fun a Bool
        postInlineUnconditional t = do
            -- See Note [Inlining criteria]
            let acceptable = costIsAcceptable t && sizeIsAcceptable t
            -- See Note [Inlining and purity]
            termIsPure <- checkPurity t
            pure $ acceptable && termIsPure

-- | Is the cost increase (in terms of evaluation work) of inlining a variable whose RHS is
-- the given term acceptable?
costIsAcceptable :: Term name uni fun a -> Bool
costIsAcceptable = \case
  Builtin{}  -> True
  Var{}      -> True
  Constant{} -> True
  Error{}    -> True
  -- This will mean that we create closures at each use site instead of
  -- once, but that's a very low cost which we're okay rounding to 0.
  LamAbs{}   -> True

  Apply{}    -> False

  Force{}    -> True
  Delay{}    -> True

-- | Is the size increase (in the AST) of inlining a variable whose RHS is
-- the given term acceptable?
sizeIsAcceptable :: Term name uni fun a -> Bool
sizeIsAcceptable = \case
  Builtin{}  -> True
  Var{}      -> True
  Error{}    -> True

  -- See Note [Differences from PIR inliner] 4
  LamAbs{}   -> False

  -- Constants can be big! We could check the size here and inline if they're
  -- small, but probably not worth it
  Constant{} -> False
  Apply{}    -> False

  Force _ t  -> sizeIsAcceptable t
  Delay _ t  -> sizeIsAcceptable t

isPure :: Term name uni fun a -> Bool
isPure = go
    where
        go = \case
            Var {}      -> True
            -- These are syntactically values that won't reduce further
            LamAbs {}   -> True
            Constant {} -> True
            Delay {}    -> True

            -- See Note [Differences from PIR inliner] 5
            _           -> False
