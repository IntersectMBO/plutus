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

import PlutusCore.Builtin qualified as PLC
import PlutusCore.Name
import PlutusCore.Quote
import PlutusCore.Rename

import PlutusCore.Annotation

import Control.Lens hiding (Strict)
import Control.Monad.Reader
import Control.Monad.State

import Data.Map qualified as Map
import Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import Prettyprinter (viaShow)

-- For unconditional inlining:

-- | Substitution range, 'SubstRng' in the paper but no 'Susp' case.
-- See Note [Inlining approach and 'Secrets of the GHC Inliner']
newtype InlineTerm tyname name uni fun ann =
    Done (Dupable (Term tyname name uni fun ann)) --out expressions

-- | Term substitution, 'Subst' in the paper.
-- A map of unprocessed variable and its substitution range.
newtype TermSubst tyname name uni fun ann =
    TermSubst { _unTermSubst :: UniqueMap TermUnique (InlineTerm tyname name uni fun ann) }
    deriving newtype (Semigroup, Monoid)

-- | Type substitution, similar to `TermSubst` but for types.
-- A map of unprocessed type variable and its substitution range.
newtype TypeSubst tyname uni ann =
    TypeSubst { _unTypeSubst :: UniqueMap TypeUnique (Dupable (Type tyname uni ann)) }
    deriving newtype (Semigroup, Monoid)

-- For call site inlining:

-- | A mapping including all non-recursive in scope variables.
newtype NonRecInScopeSet tyname name uni fun ann =
    NonRecInScopeSet
        { _unNonRecInScopeSet :: UniqueMap TermUnique (VarInfo tyname name uni fun ann)}
    deriving newtype (Semigroup, Monoid)

{-|
The (syntactic) arity of a term. That is, a record of the arguments that the
term expects before it may do some work. Since we have both type and lambda
abstractions, this is not a simple argument count, but rather a list of values
indicating whether the next argument should be a term or a type.

Note that this is the syntactic arity, i.e. it just corresponds to the number of
syntactic lambda and type abstractions on the outside of the term. It is thus
an under-approximation of how many arguments the term may need.
e.g. consider the term @let id = \x -> x in id@: the variable @id@ has syntactic
arity @[]@, but does in fact need an argument before it does any work.
-}
type Arity = [ParamKind]

-- | Info attached to a let-binding needed for call site inlining.
data VarInfo tyname name uni fun ann =
  MkVarInfo {
    varStrictness :: Strictness
    ,varDef       :: Term tyname name uni fun ann
    -- ^ its definition that has been unconditionally inlined.
    , arity       :: Arity -- ^ its arity, storing to avoid repeated calculations.
    , varBody     :: Term tyname name uni fun ann
    -- ^ the body of the function, for checking `acceptable` or not. Storing this to avoid repeated
    -- calculations.
  }
-- | Is the next argument a term or a type?
data ParamKind =
    TermParam | TypeParam
    deriving stock (Eq, Show)

instance Pretty ParamKind where
  pretty = viaShow

-- | Inliner context for both unconditional inlining and call site inlining.
-- It includes substitution for both terms and types, which is similar to 'Subst' in the paper.
-- It also includes the non recursive in-scope set for call site inlining.
data InlinerContext tyname name uni fun ann =
    InlinerContext { _termSubst :: TermSubst tyname name uni fun ann
           , _typeSubst         :: TypeSubst tyname uni ann
           , _nonRecInScopeSet  :: NonRecInScopeSet tyname name uni fun ann
          }
    deriving stock (Generic)
    deriving (Semigroup, Monoid) via
        (GenericSemigroupMonoid (InlinerContext tyname name uni fun ann))

makeLenses ''TermSubst
makeLenses ''TypeSubst
makeLenses ''NonRecInScopeSet
makeLenses ''InlinerContext

-- Helper functions:

-- | Look up the unprocessed variable in the term substitution.
lookupTerm
    :: (HasUnique name TermUnique)
    => name -- ^ The name of the variable.
    -> InlinerContext tyname name uni fun ann
    -> Maybe (InlineTerm tyname name uni fun ann)
lookupTerm n subst = lookupName n $ subst ^. termSubst . unTermSubst

-- | Insert the unprocessed variable into the term substitution.
extendTerm
    :: (HasUnique name TermUnique)
    => name -- ^ The name of the variable.
    -> InlineTerm tyname name uni fun ann -- ^ The substitution range.
    -> InlinerContext tyname name uni fun ann
    -> InlinerContext tyname name uni fun ann
extendTerm n clos subst = subst & termSubst . unTermSubst %~ insertByName n clos

-- | Look up the unprocessed type variable in the type substitution.
lookupType
    :: (HasUnique tyname TypeUnique)
    => tyname
    -> InlinerContext tyname name uni fun ann
    -> Maybe (Dupable (Type tyname uni ann))
lookupType tn subst = lookupName tn $ subst ^. typeSubst . unTypeSubst

-- | Check if the type substitution is empty.
isTypeSubstEmpty :: InlinerContext tyname name uni fun ann -> Bool
isTypeSubstEmpty (InlinerContext _ (TypeSubst tyEnv) _) = isEmpty tyEnv

-- | Insert the unprocessed type variable into the type substitution.
extendType
    :: (HasUnique tyname TypeUnique)
    => tyname -- ^ The name of the type variable.
    -> Type tyname uni ann -- ^ Its type.
    -> InlinerContext tyname name uni fun ann
    -> InlinerContext tyname name uni fun ann
extendType tn ty subst = subst &  typeSubst . unTypeSubst %~ insertByName tn (dupable ty)

-- | Look up a variable in the in scope set.
lookupVarInfo
    :: (HasUnique name TermUnique)
    => name -- ^ The name of the variable.
    -> InlinerContext tyname name uni fun ann
    -> Maybe (VarInfo tyname name uni fun ann)
lookupVarInfo n subst = lookupName n $ subst ^. nonRecInScopeSet . unNonRecInScopeSet

-- | Insert a variable into the substitution.
extendVarInfo
    :: (HasUnique name TermUnique)
    => name -- ^ The name of the variable.
    -> VarInfo tyname name uni fun ann -- ^ The variable's info.
    -> InlinerContext tyname name uni fun ann
    -> InlinerContext tyname name uni fun ann
extendVarInfo n info subst = subst & nonRecInScopeSet . unNonRecInScopeSet %~ insertByName n info

-- General infra:

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

data InlineInfo name fun ann = InlineInfo
    { _iiStrictnessMap :: Deps.StrictnessMap
    -- ^ Is it strict? Only needed for PIR, not UPLC
    , _iiUsages        :: Usages.Usages
    -- ^ how many times is it used?
    , _iiHints         :: InlineHints name ann
    -- ^ have we explicitly been told to inline?
    , _iiBuiltinVer    :: PLC.BuiltinVersion fun
    -- ^ the builtin version.
    }
makeLenses ''InlineInfo

-- Using a concrete monad makes a very large difference to the performance of this module
-- (determined from profiling)
-- | The monad the inliner runs in.
type InlineM tyname name uni fun ann =
    ReaderT (InlineInfo name fun ann) (StateT (InlinerContext tyname name uni fun ann) Quote)

-- Heuristics:

-- | Check if term is pure. See Note [Inlining and purity]
checkPurity
    :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => Term tyname name uni fun ann -> InlineM tyname name uni fun ann Bool
checkPurity t = do
    strctMap <- view iiStrictnessMap
    builtinVer <- view iiBuiltinVer
    let strictnessFun n' = Map.findWithDefault NonStrict (n' ^. theUnique) strctMap
    pure $ isPure builtinVer strictnessFun t

-- | Checks if a binding is pure, i.e. will evaluating it have effects
isTermBindingPure :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => Strictness
    -> Term tyname name uni fun ann
    -> InlineM tyname name uni fun ann Bool
isTermBindingPure s tm =
    case s of
        -- For non-strict bindings, the effects would have occurred at the call sites anyway.
        NonStrict -> pure True
        Strict    -> checkPurity tm

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

nameUsedAtMostOnce :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => name
    -> InlineM tyname name uni fun ann Bool
nameUsedAtMostOnce n = do
    usgs <- view iiUsages
    -- 'inlining' terms used 0 times is a cheap way to remove dead code while we're here
    pure $ Usages.getUsageCount n usgs <= 1

effectSafe :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => Term tyname name uni fun ann
    -> Strictness
    -> name
    -> Bool -- ^ is it pure?
    -> InlineM tyname name uni fun ann Bool
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
acceptable ::  Term tyname name uni fun ann -> Bool
acceptable t =
    -- See Note [Inlining criteria]
    costIsAcceptable t && sizeIsAcceptable t

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
costIsAcceptable :: Term tyname name uni fun ann -> Bool
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
sizeIsAcceptable :: Term tyname name uni fun ann -> Bool
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

-- | Is this an utterly trivial type which might as well be inlined?
trivialType :: Type tyname uni ann -> Bool
trivialType = \case
    TyBuiltin{} -> True
    TyVar{}     -> True
    _           -> False
