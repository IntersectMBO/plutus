{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeFamilies     #-}

{- | Types and their functions, and general utility (including heuristics) for inlining. -}

module PlutusIR.Transform.Inline.Utils where

import PlutusCore.Annotation
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Name
import PlutusCore.Quote
import PlutusCore.Rename
import PlutusCore.Subst (typeSubstTyNamesM)
import PlutusIR
import PlutusIR.Analysis.Dependencies qualified as Deps
import PlutusIR.Analysis.Usages qualified as Usages
import PlutusIR.Purity (FirstEffectfulTerm (..), firstEffectfulTerm, isPure)
import PlutusIR.Transform.Rename ()
import PlutusPrelude

import Control.Lens hiding (Strict)
import Control.Monad.Extra
import Control.Monad.Reader
import Control.Monad.State

import Data.Map qualified as Map
import Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import Prettyprinter (viaShow)

-- General infra:

type ExternalConstraints tyname name uni fun m =
    ( HasUnique name TermUnique
    , HasUnique tyname TypeUnique
    , Eq name
    , Eq tyname
    , PLC.ToBuiltinMeaning uni fun
    , MonadQuote m
    )

type InliningConstraints tyname name uni fun =
    ( HasUnique name TermUnique
    , HasUnique tyname TypeUnique
    , Eq name
    , Eq tyname
    , PLC.ToBuiltinMeaning uni fun
    )

-- | Information used by the inliner that is constant across its operation.
-- This includes some contextual and configuration information, and also some
-- pre-computed information about the program.
--
-- See [Inlining and global uniqueness] for caveats about this information.
data InlineInfo name fun ann = InlineInfo
    { _iiStrictnessMap           :: Deps.StrictnessMap
    -- ^ Is it strict? Only needed for PIR, not UPLC
    , _iiUsages                  :: Usages.Usages
    -- ^ how many times is it used?
    , _iiHints                   :: InlineHints name ann
    -- ^ have we explicitly been told to inline?
    , _iiBuiltinSemanticsVariant :: PLC.BuiltinSemanticsVariant fun
    -- ^ the semantics variant.
    }
makeLenses ''InlineInfo

-- Using a concrete monad makes a very large difference to the performance of this module
-- (determined from profiling)
-- | The monad the inliner runs in.
type InlineM tyname name uni fun ann =
    ReaderT (InlineInfo name fun ann) (StateT (InlinerState tyname name uni fun ann) Quote)
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
type Arity tyname name = [Param tyname name]

-- | Info attached to a let-binding needed for call site inlining.
data VarInfo tyname name uni fun ann = MkVarInfo
    { varStrictness :: Strictness
    , varRhs        :: InlineTerm tyname name uni fun ann
    -- ^ its definition that has been unconditionally inlined, as an `InlineTerm`. To preserve
    -- global uniqueness, we rename before substituting in.
    }
-- | Is the next argument a term or a type?
data Param tyname name =
    TermParam name | TypeParam tyname
    deriving stock (Show)

instance (Show tyname, Show name) => Pretty (Param tyname name) where
  pretty = viaShow

-- | Inliner context for both unconditional inlining and call site inlining.
-- It includes substitution for both terms and types, which is similar to 'Subst' in the paper.
-- It also includes the non recursive in-scope set for call site inlining.
data InlinerState tyname name uni fun ann =
    InlinerState { _termSubst  :: TermSubst tyname name uni fun ann
           , _typeSubst        :: TypeSubst tyname uni ann
           , _nonRecInScopeSet :: NonRecInScopeSet tyname name uni fun ann
          }
    deriving stock (Generic)
    deriving (Semigroup, Monoid) via
        (GenericSemigroupMonoid (InlinerState tyname name uni fun ann))

makeLenses ''TermSubst
makeLenses ''TypeSubst
makeLenses ''NonRecInScopeSet
makeLenses ''InlinerState

-- Helper functions:

-- | Look up the unprocessed variable in the term substitution.
lookupTerm
    :: (HasUnique name TermUnique)
    => name -- ^ The name of the variable.
    -> InlinerState tyname name uni fun ann
    -> Maybe (InlineTerm tyname name uni fun ann)
lookupTerm n s = lookupName n $ s ^. termSubst . unTermSubst

-- | Insert the unprocessed variable into the term substitution.
extendTerm
    :: (HasUnique name TermUnique)
    => name -- ^ The name of the variable.
    -> InlineTerm tyname name uni fun ann -- ^ The substitution range.
    -> InlinerState tyname name uni fun ann
    -> InlinerState tyname name uni fun ann
extendTerm n clos s = s & termSubst . unTermSubst %~ insertByName n clos

-- | Look up the unprocessed type variable in the type substitution.
lookupType
    :: (HasUnique tyname TypeUnique)
    => tyname
    -> InlinerState tyname name uni fun ann
    -> Maybe (Dupable (Type tyname uni ann))
lookupType tn s = lookupName tn $ s ^. typeSubst . unTypeSubst

-- | Check if the type substitution is empty.
isTypeSubstEmpty :: InlinerState tyname name uni fun ann -> Bool
isTypeSubstEmpty (InlinerState _ (TypeSubst tyEnv) _) = isEmpty tyEnv

-- | Insert the unprocessed type variable into the type substitution.
extendType
    :: (HasUnique tyname TypeUnique)
    => tyname -- ^ The name of the type variable.
    -> Type tyname uni ann -- ^ Its type.
    -> InlinerState tyname name uni fun ann
    -> InlinerState tyname name uni fun ann
extendType tn ty s = s &  typeSubst . unTypeSubst %~ insertByName tn (dupable ty)

-- | Look up a variable in the in scope set.
lookupVarInfo
    :: (HasUnique name TermUnique)
    => name -- ^ The name of the variable.
    -> InlinerState tyname name uni fun ann
    -> Maybe (VarInfo tyname name uni fun ann)
lookupVarInfo n s = lookupName n $ s ^. nonRecInScopeSet . unNonRecInScopeSet

-- | Insert a variable into the substitution.
extendVarInfo
    :: (HasUnique name TermUnique)
    => name -- ^ The name of the variable.
    -> VarInfo tyname name uni fun ann -- ^ The variable's info.
    -> InlinerState tyname name uni fun ann
    -> InlinerState tyname name uni fun ann
extendVarInfo n info s = s & nonRecInScopeSet . unNonRecInScopeSet %~ insertByName n info


applyTypeSubstitution :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => Type tyname uni ann
    -> InlineM tyname name uni fun ann (Type tyname uni ann)
applyTypeSubstitution t = gets isTypeSubstEmpty >>= \case
    -- The type substitution is very often empty, and there are lots of types in the program,
    -- so this saves a lot of work (determined from profiling)
    True -> pure t
    _    -> typeSubstTyNamesM substTyName t

-- See Note [Inlining and global uniqueness]
substTyName :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => tyname
    -> InlineM tyname name uni fun ann (Maybe (Type tyname uni ann))
substTyName tyname = gets (lookupType tyname) >>= traverse liftDupable

-- See Note [Inlining and global uniqueness]
substName :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => name
    -> InlineM tyname name uni fun ann (Maybe (Term tyname name uni fun ann))
substName name = gets (lookupTerm name) >>= traverse renameTerm

-- See Note [Inlining approach and 'Secrets of the GHC Inliner']
-- Already processed term, just rename and put it in, don't do any further optimization here.
renameTerm :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => InlineTerm tyname name uni fun ann
    -> InlineM tyname name uni fun ann (Term tyname name uni fun ann)
renameTerm (Done t) = liftDupable t

{- Note [Renaming strategy]
Since we assume global uniqueness, we can take a slightly different approach to
renaming:  we rename the term we are substituting in, instead of renaming
every binder that our substitution encounters, which should guarantee that we
avoid any variable capture.

We rename both terms and types as both may have binders in them.
-}

-- Heuristics:

-- | Check if term is pure. See Note [Inlining and purity]
checkPurity
    :: forall tyname name uni fun ann. InliningConstraints tyname name uni fun
    => Term tyname name uni fun ann -> InlineM tyname name uni fun ann Bool
checkPurity t = do
    strctMap <- view iiStrictnessMap
    builtinSemVar <- view iiBuiltinSemanticsVariant
    let strictnessFun n' = Map.findWithDefault NonStrict (n' ^. theUnique) strctMap
    pure $ isPure builtinSemVar strictnessFun t

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
            Just (EffectfulTerm (Var _ n')) -> n == n'
            _                               -> False
    pure $ case s of
        Strict    -> purity || immediatelyEvaluated
        NonStrict -> True

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

-- See Note [Inlining criteria]
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

  -- Inlining constructors of size 1 or 0 seems okay, but does result in doing
  -- the work for the elements at each use site.
  Constr _ _ _ es  -> case es of
      []  -> True
      [e] -> costIsAcceptable e
      _   -> False
  -- Inlining a case means redoing the match at each use site
  Case{} -> False

  -- Arguably we could allow these two, but they're uncommon anyway
  IWrap{}    -> False
  Unwrap{}   -> False

  Apply{}    -> False
  TyInst{}   -> False
  Let{}      -> False

-- See Note [Inlining criteria]
-- | Is the size increase (in the AST) of inlining a variable whose RHS is
-- the given term acceptable?
sizeIsAcceptable :: Term tyname name uni fun ann -> Bool
sizeIsAcceptable = \case
  Builtin{}  -> True
  Var{}      -> True
  Error{}    -> True
  LamAbs {}  -> False
  TyAbs {}   -> False

  -- Inlining constructors of size 1 or 0 seems okay
  Constr _ _ _ es  -> case es of
      []  -> True
      [e] -> sizeIsAcceptable e
      _   -> False
  -- Cases are pretty big, due to the case branches
  Case{} -> False

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

shouldUnconditionallyInline ::
  (InliningConstraints tyname name uni fun) =>
  Strictness ->
  name ->
  Term tyname name uni fun ann ->
  Term tyname name uni fun ann ->
  InlineM tyname name uni fun ann Bool
shouldUnconditionallyInline s n rhs body = preUnconditional ||^ postUnconditional
  where
    -- similar to the paper, preUnconditional inlining checks that the binder is 'OnceSafe'.
    -- I.e., it's used at most once AND it neither duplicate code or work.
    -- While we don't check for lambda etc like in the paper, `effectSafe` ensures that it
    -- isn't doing any substantial work.
    -- We actually also inline 'Dead' binders (i.e., remove dead code) here.
    preUnconditional = do
      isTermPure <- checkPurity rhs
      nameUsedAtMostOnce n &&^ effectSafe body s n isTermPure

    -- See Note [Inlining approach and 'Secrets of the GHC Inliner'] and [Inlining and
    -- purity]. This is the case where we don't know that the number of occurrences is
    -- exactly one, so there's no point checking if the term is immediately evaluated.
    postUnconditional = do
      isBindingPure <- isTermBindingPure s rhs
      pure $ isBindingPure && sizeIsAcceptable rhs && costIsAcceptable rhs
