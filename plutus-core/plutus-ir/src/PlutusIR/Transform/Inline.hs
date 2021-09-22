{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}
{-|
A simple inlining pass.

The point of this pass is mainly to tidy up the code, not to particularly optimize performance.
In particular, we want to get rid of "trivial" let bindings which the Plutus Tx compiler sometimes creates.
-}
module PlutusIR.Transform.Inline (inline) where

import           PlutusIR
import qualified PlutusIR.Analysis.Dependencies as Deps
import qualified PlutusIR.Analysis.Usages       as Usages
import           PlutusIR.MkPir
import           PlutusIR.Purity
import           PlutusIR.Transform.Rename      ()
import           PlutusPrelude

import qualified PlutusCore                     as PLC
import qualified PlutusCore.Constant.Meaning    as PLC
import           PlutusCore.Name
import           PlutusCore.Quote
import           PlutusCore.Subst               (typeSubstTyNamesM)

import           Control.Lens                   hiding (Strict)
import           Control.Monad.Reader
import           Control.Monad.State

import qualified Algebra.Graph                  as G
import qualified Data.Map                       as Map
import           Data.Semigroup.Generic         (GenericSemigroupMonoid (..))
import           Witherable

{- Note [Inlining approach and 'Secrets of the GHC Inliner']
The approach we take is more-or-less exactly taken from 'Secrets of the GHC Inliner'.

Overall, the cause of differences is that we are largely trying to just clean up some
basic issues, not do serious optimization. In many cases we've already run the GHC simplifier
on our input!

We differ from the paper a few ways, mostly leaving things out:

Functionality
------------

PreInlineUncoditional: we don't do it, since we don't bother using usage information.
We *could* do it, but it doesn't seem worth it. We also don't need to worry about
inlining nested let-bindings, since we don't inline any.

CallSiteInline: not worth it.

Inlining recursive bindings: not worth it, complicated.

Context-based inlining: we don't do CallSiteInline, so no point.

Beta reduction: not worth it, but would be easy. We could do the inlining of the argument
here and also detect dead immediately-applied-lambdas in the dead code pass.

Implementation
--------------

In-scope set: we don't bother keeping it, since we only ever substitute in things that
don't have bound variables. This is largely because we don't do PreInlineUnconditional, which
would inline big things that were only used once, including lambdas etc.

Suspended substitutions for values: we don't do it, since you only need it for
PreInlineUnconditional

Optimization after substituting in DoneExprs: we can't make different inlining decisions
contextually, so there's no point doing this.
-}


-- 'SubstRng' in the paper, no 'Susp' case
-- See Note [Inlining approach and 'Secrets of the GHC Inliner']
newtype InlineTerm tyname name uni fun a = Done (Term tyname name uni fun a)

newtype TermEnv tyname name uni fun a = TermEnv { _unTermEnv :: UniqueMap TermUnique (InlineTerm tyname name uni fun a) }
    deriving newtype (Semigroup, Monoid)

newtype TypeEnv tyname uni a = TypeEnv { _unTypeEnv :: UniqueMap TypeUnique (Type tyname uni a) }
    deriving newtype (Semigroup, Monoid)

data Subst tyname name uni fun a = Subst { _termEnv :: TermEnv tyname name uni fun a
                                         , _typeEnv :: TypeEnv tyname uni a
                                         }
    deriving stock (Generic)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid (Subst tyname name uni fun a))

makeLenses ''TermEnv
makeLenses ''TypeEnv
makeLenses ''Subst

type ExternalConstraints tyname name uni fun m =
    ( HasUnique name TermUnique
    , HasUnique tyname TypeUnique
    , PLC.ToBuiltinMeaning uni fun
    , MonadQuote m
    )

type InliningConstraints tyname name uni fun =
    ( HasUnique name TermUnique
    , HasUnique tyname TypeUnique
    , PLC.ToBuiltinMeaning uni fun
    )


data InlineInfo = InlineInfo { _strictnessMap :: Deps.StrictnessMap
                             , _usages        :: Usages.Usages
                             }

-- Using a concrete monad makes a very large difference to the performance of this module (determined from profiling)
type InlineM tyname name uni fun a = ReaderT InlineInfo (StateT (Subst tyname name uni fun a) Quote)

lookupTerm
    :: (HasUnique name TermUnique)
    => name
    -> Subst tyname name uni fun a
    -> Maybe (InlineTerm tyname name uni fun a)
lookupTerm n subst = lookupName n $ subst ^. termEnv . unTermEnv

extendTerm
    :: (HasUnique name TermUnique)
    => name
    -> InlineTerm tyname name uni fun a
    -> Subst tyname name uni fun a
    -> Subst tyname name uni fun a
extendTerm n clos subst = subst & termEnv . unTermEnv %~ insertByName n clos

lookupType
    :: (HasUnique tyname TypeUnique)
    => tyname
    -> Subst tyname name uni fun a
    -> Maybe (Type tyname uni a)
lookupType tn subst = lookupName tn $ subst ^. typeEnv . unTypeEnv

isTypeSubstEmpty :: Subst tyname name uni fun a -> Bool
isTypeSubstEmpty (Subst _ (TypeEnv tyEnv)) = isEmpty tyEnv

extendType
    :: (HasUnique tyname TypeUnique)
    => tyname
    -> Type tyname uni a
    -> Subst tyname name uni fun a
    -> Subst tyname name uni fun a
extendType tn ty subst = subst &  typeEnv . unTypeEnv %~ insertByName tn ty

{- Note [Inlining and global uniqueness]
Inlining relies on global uniqueness (we store things in a unique map), and *does* currently
preserve it because we don't currently inline anything with binders.

If we do start inlining things with binders in them, we should probably try and preserve it by
doing something like 'The rapier' section from the paper. We could also just bite the bullet
and rename everything when we substitute in, which GHC considers too expensive but we might accept.
-}

-- | Inline simple bindings. Relies on global uniqueness, and preserves it.
-- See Note [Inlining and global uniqueness]
inline
    :: ExternalConstraints tyname name uni fun m
    => Term tyname name uni fun a
    -> m (Term tyname name uni fun a)
inline t = let
        inlineInfo :: InlineInfo
        inlineInfo = InlineInfo (snd deps) usgs
        -- We actually just want the variable strictness information here!
        deps :: (G.Graph Deps.Node, Map.Map PLC.Unique Strictness)
        deps = Deps.runTermDeps t
        usgs :: Map.Map Unique Int
        usgs = Usages.runTermUsages t
    in liftQuote $ flip evalStateT mempty $ flip runReaderT inlineInfo $ processTerm t

{- Note [Removing inlined bindings]
We *do* remove bindings that we inline (since we only do unconditional inlining). We *could*
leave this to the dead code pass, but it's helpful to do it here.
Crucially, we have to do the same reasoning wrt strict bindings and purity (see Note [Inlining and purity]):
we can only inline *pure* strict bindings, which is effectively the same as what we do in the dead
code pass.

Annoyingly, this requires us to redo the analysis that we do for the dead binding pass.
TODO: merge them or figure out a way to share more work, especially since there's similar logic.
This might mean reinventing GHC's OccAnal...
-}

processTerm
    :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => Term tyname name uni fun a
    -> InlineM tyname name uni fun a (Term tyname name uni fun a)
processTerm = handleTerm <=< traverseOf termSubtypes applyTypeSubstitution where
    handleTerm :: Term tyname name uni fun a -> InlineM tyname name uni fun a (Term tyname name uni fun a)
    handleTerm = \case
        v@(Var _ n) -> fromMaybe v <$> substName n
        Let a NonRec bs t -> do
            -- Process bindings, eliminating those which will be inlined unconditionally,
            -- and accumulating the new substitutions
            -- See Note [Removing inlined bindings]
            -- Note that we don't *remove* the bindings or scope the state, so the state will carry over
            -- into "sibling" terms. This is fine because we have global uniqueness
            -- (see Note [Inlining and global uniqueness]), if somewhat wasteful.
            bs' <- wither processSingleBinding (toList bs)
            t' <- processTerm t
            -- Use 'mkLet': we're using lists of bindings rather than NonEmpty since we might actually
            -- have got rid of all of them!
            pure $ mkLet a NonRec bs' t'
        -- We cannot currently soundly do beta for types (see SCP-2570), so we just recognize
        -- immediately instantiated type abstractions here directly.
        (TyInst a (TyAbs a' tn k t) rhs) -> do
            b' <- maybeAddTySubst tn rhs
            t' <- processTerm t
            case b' of
                Just rhs' -> pure $ TyInst a (TyAbs a' tn k t') rhs'
                Nothing   -> pure t'
        -- This includes recursive let terms, we don't even consider inlining them at the moment
        t -> forMOf termSubterms t processTerm
    applyTypeSubstitution :: Type tyname uni a -> InlineM tyname name uni fun a (Type tyname uni a)
    applyTypeSubstitution t = gets isTypeSubstEmpty >>= \case
        -- The type substitution is very often empty, and there are lots of types in the program, so this saves a lot of work (determined from profiling)
        True -> pure t
        _    -> typeSubstTyNamesM substTyName t
    -- See Note [Renaming strategy]
    substTyName :: tyname -> InlineM tyname name uni fun a (Maybe (Type tyname uni a))
    substTyName tyname = gets (lookupType tyname) >>= traverse PLC.rename
    -- See Note [Renaming strategy]
    substName :: name -> InlineM tyname name uni fun a (Maybe (Term tyname name uni fun a))
    substName name = gets (lookupTerm name) >>= traverse renameTerm
    -- See Note [Inlining approach and 'Secrets of the GHC Inliner']
    renameTerm :: InlineTerm tyname name uni fun a -> InlineM tyname name uni fun a (Term tyname name uni fun a)
    renameTerm = \case
        -- Already processed term, just rename and put it in, don't do any
        -- further optimization here.
        Done t -> PLC.rename t

{- Note [Renaming strategy]
Since we assume global uniqueness, we can take a slightly different approach to
renaming:  we rename the term we are substituting in, instead of renaming
every binder that our substitution encounters, which should guarantee that we
avoid any variable capture.

We rename both terms and types as both may have binders in them.
-}

processSingleBinding
    :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => Binding tyname name uni fun a
    -> InlineM tyname name uni fun a (Maybe (Binding tyname name uni fun a))
processSingleBinding = \case
    TermBind a s v@(VarDecl _ n _) rhs -> do
        maybeRhs' <- maybeAddSubst s n rhs
        pure $ TermBind a s v <$> maybeRhs'
    TypeBind a v@(TyVarDecl _ n _) rhs -> do
        maybeRhs' <- maybeAddTySubst n rhs
        pure $ TypeBind a v <$> maybeRhs'
    -- Just process all the subterms
    b -> Just <$> forMOf bindingSubterms b processTerm

-- NOTE:  Nothing means that we are inlining the term:
--   * we have extended the substitution, and
--   * we are removing the binding (hence we return Nothing)
maybeAddSubst
    :: forall tyname name uni fun a. InliningConstraints tyname name uni fun
    => Strictness
    -> name
    -> Term tyname name uni fun a
    -> InlineM tyname name uni fun a (Maybe (Term tyname name uni fun a))
maybeAddSubst s n rhs = do
    rhs' <- processTerm rhs
    preUnconditional <- preInlineUnconditional rhs'
    if preUnconditional
    then extendAndDrop (Done rhs')
    else do
        -- See Note [Inlining approach and 'Secrets of the GHC Inliner']
        postUnconditional <- postInlineUnconditional rhs'
        if postUnconditional
        then extendAndDrop (Done rhs')
        else pure $ Just rhs'
    where
        extendAndDrop :: forall b . InlineTerm tyname name uni fun a -> InlineM tyname name uni fun a (Maybe b)
        extendAndDrop t = modify' (extendTerm n t) >> pure Nothing

        checkPurity :: Term tyname name uni fun a -> InlineM tyname name uni fun a Bool
        checkPurity t = do
            strctMap <- asks _strictnessMap
            let strictnessFun = \n' -> Map.findWithDefault NonStrict (n' ^. theUnique) strctMap
            pure $ isPure strictnessFun t

        preInlineUnconditional :: Term tyname name uni fun a -> InlineM tyname name uni fun a Bool
        preInlineUnconditional t = do
            usgs <- asks _usages
            let termIsUsedOnce = Usages.isUsedOnce n usgs
            -- See Note [Inlining and purity]
            termIsPure <- checkPurity t
            pure $ termIsUsedOnce && case s of { Strict -> termIsPure; NonStrict -> True; }

        -- | Should we inline? Should only inline things that won't duplicate work or code.
        -- See Note [Inlining approach and 'Secrets of the GHC Inliner']
        postInlineUnconditional ::  Term tyname name uni fun a -> InlineM tyname name uni fun a Bool
        postInlineUnconditional t = do
            -- See Note [Inlining criteria]
            let termIsTrivial = trivialTerm t
            -- See Note [Inlining and purity]
            termIsPure <- checkPurity t
            pure $ termIsTrivial && case s of { Strict -> termIsPure; NonStrict -> True; }

{- Note [Inlining criteria]
What gets inlined? We don't really care about performance here, so we're really just
angling to simplify the code without making things worse.

The obvious candidates are tiny things like builtins, variables, or constants.
We could also consider inlining variables with arbitrary RHSs that are used only
once, but we don't do that currently.
-}

{- Note [Inlining and purity]
When can we inline something that might have effects? We must remember that we often also
remove a binding that we inline.

For strict bindings, the answer is that we can't: we will delay the effects to the use site,
so they may happen multiple times (or none). So we can only inline bindings whose RHS is pure.

For non-strict bindings, the effects already happened at the use site, so it's fine to inline it
unconditionally.
-}

maybeAddTySubst
    :: forall tyname name uni fun a . InliningConstraints tyname name uni fun
    => tyname
    -> Type tyname uni a
    -> InlineM tyname name uni fun a (Maybe (Type tyname uni a))
maybeAddTySubst tn rhs = do
    usgs <- asks _usages
    -- No need for multiple phases here
    let typeIsUsedOnce = Usages.isUsedOnce tn usgs
    if typeIsUsedOnce || trivialType rhs
    then do
        modify' (extendType tn rhs)
        pure Nothing
    else pure $ Just rhs

-- | Is this a an utterly trivial term which might as well be inlined?
trivialTerm :: Term tyname name uni fun a -> Bool
trivialTerm = \case
    Builtin{}  -> True
    Var{}      -> True
    -- TODO: Should this depend on the size of the constant?
    Constant{} -> True
    _          -> False

-- | Is this a an utterly trivial type which might as well be inlined?
trivialType :: Type tyname uni a -> Bool
trivialType = \case
    TyBuiltin{} -> True
    TyVar{}     -> True
    _           -> False
