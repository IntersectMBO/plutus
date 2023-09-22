-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
module PlutusIR.Transform.LetFloatOut (floatTerm) where

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Name qualified as PLC
import PlutusIR
import PlutusIR.Purity
import PlutusIR.Subst

import Control.Arrow ((>>>))
import Control.Lens hiding (Strict)
import Control.Monad.Extra
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Coerce
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as M
import Data.Map.Monoidal qualified as MM
import Data.Semigroup.Foldable
import Data.Semigroup.Generic
import Data.Set qualified as S
import Data.Set.Lens (setOf)
import GHC.Generics
import PlutusIR.Analysis.Builtins
import PlutusIR.Analysis.VarInfo

{- Note [Let Floating pass]

The goal of this pass is to move (float) let-bindings as outwards as possible,
without breaking the scoping & meaning of the original PIR term.

This transformation (a.k.a. full laziness), together with a possible implementation
is described in Peyton Jones, Simon, Will Partain, and Andre Santos. "Let-Floating: Moving Bindings to Give Faster Programs."
In Proceedings of the First ACM SIGPLAN International Conference on Functional Programming, 1-12.
ICFP '96. New York, NY, USA: ACM, 1996. https://doi.org/10.1145/232627.232630.

An implementation, as described in the paper, is comprised of two "passes":

1) a "mark" pass to traverse the term tree and
  - in case of lam/Lam, mark this lam/Lam name with current depth, and
    increase the depth for the lam/Lam's-abstraction body term and recurse.
  - in case of a Letrecgroup, collect the free term&type variables and mark every let-introduced name
    with the maximum depth among all the free variables (the free variables should be already marked)
  - in case of letnonrec group, you can treat it the same as (letrec g in letrec gs)

2) a "float-back" pass which, given the collected marks,
   traverses the term tree again and whenever a let(rec or nonrec) is encountered,
   decides locally if it is worth to float the current let outwards at its marked depth.
   If yes, the let-group's binding is floated exactly outside a lambda abstraction that has lam_depth=let_depth+1

There are some  differences with the paper's described implementation above, namely:

a) we use 3 passes. the 1st pass is similar to the original; a second pass
"cleans" the term from all the to-be-floated lets and stores them in a separate table.
the 3rd pass is responsible to float back the removed lets inside the cleaned term
according to their markers. So we use an extra pass because we float back lets in a global fashion,
instead of deciding locally.

b) Since the 3rd (float-back) pass operates on the cleaned term, we have lost
the original location of the lets, so we cannot float them "right outside" the **maximum-independent lambda-abstraction**,
but we float them "right inside" the maximum **dependent** lambda-abstraction's body. This has the downside
of allocating&holding the lets for longer than needed, but will not alter the meaning of the original PIR term.

c) Since PIR has strict (compared to the paper's lazy-only lang), we have to make
sure that any let-group containing at least one **effectful** (i.e. non-pure) strict binding is
not floated at all. See the implementation of 'hasNoEffects'.

This does not mean that such an "effectful" let
will appear in the same absolute location as the original term:
An outside/parent let may float around, changing the child's (effectful let) absolute location;
however, the child's relative location to the parent *must* remain the same. Consider this example:

`... let (nonstrict) x1= (let (strict) x2 = error in rhs1) in body1`

The parent of x2 is x1 and it is floatable
The child of x1 is x2 and it is unmovable
The x2 binding will not move with respect to x1, but its original absolute program location may change,
because the parent may float upwards somewhere else.

Since another let variable may depend on such *effectful* let, and to preserve the execution order,
we treat an effectful also as an "anchor", by increasing the current depth
both on entering any of its rhs'es *and* inside its inTerm.
-}

newtype Depth = Depth Int
    deriving newtype (Eq, Ord, Show, Num)

{-| Position of an anchor (lam,Lam,unfloatable-let or Top).
The original paper's algorithm relies just on using the depth as the anchor's position;
for us this is no enough, because we act mark/remove/float globally and the depth is not globally-unique.
To fix this, we use an extra "representative" identifier (PLC.Unique) of the anchor.
Since (unfloatable) lets can also be anchors, we also use an extra 'PosType' to differentiate
between two cases of a let-anchor, see 'PosType'.
-}
data Pos = Pos
    { _posDepth  :: Depth
    , _posUnique :: PLC.Unique -- ^ The lam name or Lam tyname or Let's representative unique
    , _posType   :: PosType
    }
    deriving stock (Eq, Ord, Show)

{-| The type of the anchor's position. We only need this because
we need to differentiate between two cases of a 'let-anchor' position:

A floatable let-binding can (maximally) depend on an (unfloatable, effectful) let anchor,
which means that it will either float in two different places, depending upon the floatable let's original location:

a) floated *next to* the let-anchor it depends upon (inside its let-group), if it originated from the rhs of the let-anchor
b) floated directly under the `in` of the let-anchor it depends upon, if it originated from the inTerm of the let-anchor.
-}
data PosType = LamBody -- ^ lam, Lam, let body, or Top
             | LetRhs -- ^ let rhs
             deriving stock (Eq, Ord, Show)

topPos :: Pos
topPos = Pos topDepth topUnique topType

-- | For simplicity, the top position is also linked to a unique number
-- chosen to not clash with any actual uniques of names/tynames of the program
topUnique :: PLC.Unique
topUnique = coerce (-1 :: Int)

-- | arbitrarily chosen
topDepth :: Depth
topDepth = -1

-- | arbitrary chosen as LamBody, because top can be imagined as a global inbody (of an empty letterm)
topType :: PosType
topType = LamBody

-- | Arbitrary: return a single unique among all the introduced uniques of the given letgroup.
representativeBindingUnique
    :: (PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique)
    => NE.NonEmpty (Binding tyname name uni fun a) -> PLC.Unique
representativeBindingUnique =
    -- Arbitrary: select the first unique from the representative binding
    first1Of bindingIds . representativeBinding
  where
    --  Arbitrary: a binding to be used as representative binding in MARKING the group of bindings.
    representativeBinding :: NE.NonEmpty (Binding tyname name uni fun a) -> Binding tyname name uni fun a
    representativeBinding = NE.head

-- | Every term and type variable in current scope
-- is paired with its own computed marker (maximum dependent position)
-- OPTIMIZE: use UniqueMap instead
type Scope = M.Map PLC.Unique Pos

-- | The first pass has a reader context of current depth, and (term&type)variables in scope.
data MarkCtx tyname name uni fun = MarkCtx
    { _markCtxDepth     :: Depth
    , _markCtxScope     :: Scope
    , _markBuiltinsInfo :: BuiltinsInfo uni fun
    , _markVarsInfo     :: VarsInfo tyname name
    }
makeLenses ''MarkCtx

-- | The result of the first pass is a subset(union of all computed scopes).
-- This subset contains only the marks of the floatable lets.
type Marks = Scope

{-|
A 'BindingGrp' is a group of bindings and a *minimum* recursivity for the group.
We use this intermediate structure when tracking groups of bindings to be floated or re-inserted.

It's convenient when doing this work to be able to combine binding groups (with the 'Semigroup') instance.
However, appending 'BindingGrp's does not account for the possibility that binding groups may *share*
variables. This means that the combination of multiple non-recursive binding groups may be recursive.
As such, if you have reason to believe that the variables used by the combined binding groups may not be disjoint,
you should manually require the term to be recursive when you convert back to a let term with 'bindingGrpToLet'.
-}
data BindingGrp tyname name uni fun a = BindingGrp {
    _bgAnn      :: a,
    _bgRec      :: Recursivity,
    _bgBindings :: NE.NonEmpty (Binding tyname name uni fun a)
    }
    deriving stock Generic
    deriving Semigroup via (GenericSemigroupMonoid (BindingGrp tyname name uni fun a))
-- Note on Semigroup: appending bindingGroups will not try to fix the well-scopedness by
-- rearranging any bindings or promoting to a Rec if bindings in case some bindinings refer to each other.
makeLenses ''BindingGrp

-- | Turn a 'BindingGrp' into a let, when given a minimum recursivity and let body.
bindingGrpToLet :: Recursivity
        -> BindingGrp tyname name uni fun a
        -> (Term tyname name uni fun a -> Term tyname name uni fun a)
bindingGrpToLet r (BindingGrp a r' bs) = Let a (r<>r') bs

-- | A store of lets to be floated at their new position
type FloatTable tyname name uni fun a = MM.MonoidalMap Pos (NE.NonEmpty (BindingGrp tyname name uni fun a))

-- | The 1st pass of marking floatable lets
mark :: forall tyname name uni fun a.
      (Ord tyname, Ord name, PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique, PLC.ToBuiltinMeaning uni fun)
     => BuiltinsInfo uni fun
     -> Term tyname name uni fun a
     -> Marks
mark binfo tm = snd $ runWriter $ flip runReaderT (MarkCtx topDepth mempty binfo (termVarInfo tm)) $ go tm
  where
    go :: Term tyname name uni fun a -> ReaderT (MarkCtx tyname name uni fun) (Writer Marks) ()
    go = breakNonRec >>> \case
        -- lam/Lam are treated the same.
        LamAbs _ n _ tBody  -> withLam n $ go tBody
        TyAbs _ n _ tBody   -> withAbs n $ go tBody

        -- main operation: for letrec or single letnonrec
        Let ann r bs@(representativeBindingUnique -> letU) tIn ->
          let letN = BindingGrp ann r bs in
          ifM (floatable letN)
          -- then
          (do
            scope <- view markCtxScope
            let freeVars =
                    -- if Rec, remove the here-bindings from free
                    ifRec r (S.\\ setOf (traversed.bindingIds) bs) $
                       calcFreeVars letN

            -- The "heart" of the algorithm: the future position to float this let to
            -- is determined as the maximum among its dependencies (free vars).
            let floatPos@(Pos floatDepth _ _) = maxPos $ scope `M.restrictKeys` freeVars

            -- visit the rhs'es
            -- IMPORTANT: inside the rhs, act like the current depth
            -- is the future floated depth of this rhs.
            withDepth (const floatDepth) $
                -- if rec, then its bindings are in scope in the rhs'es
                ifRec r (withBs bs floatPos) $
                    traverseOf_ (traversed . bindingSubterms) go bs

            -- visit the inTerm
            -- bindings are inscope in the InTerm for both rec&nonrec
            withBs bs floatPos $ go tIn

            -- collect here the new mark and propagate all
            tell $ M.singleton letU floatPos
          )
          -- else
          $ do
            -- since it is unfloatable (effectful), this let is a new anchor
            -- acts as anchor both in rhs'es and inTerm
            withDepth (+1) $ do
                depth <- view markCtxDepth
                let toPos = Pos depth letU
                -- visit the rhs'es
                -- if rec, then its bindings are in scope in the rhs'es
                ifRec r (withBs bs $ toPos LetRhs) $ traverseOf_ (traversed . bindingSubterms) go bs

                -- bindings are inscope in the InTerm for both rec&nonrec
                withBs bs (toPos LamBody) $ go tIn

        -- descend and collect
        t -> traverseOf_ termSubterms go t

-- | Given a 'BindingGrp', calculate its free vars and free tyvars and collect them in a set.
calcFreeVars :: forall tyname name uni fun a.
             (Ord tyname, Ord name, PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique)
             => BindingGrp tyname name uni fun a
             -> S.Set PLC.Unique
calcFreeVars (BindingGrp _ r bs) = foldMap1 calcBinding bs
  where
    -- given a binding return all its free term *AND* free type variables
    calcBinding :: Binding tyname name uni fun a -> S.Set PLC.Unique
    calcBinding b =
        setOf (fvBinding . PLC.theUnique) b
        <> setOf (ftvBinding r . PLC.theUnique) b

-- | The second pass of cleaning the term of the floatable lets, and placing them in a separate map
-- OPTIMIZE: use State for building the FloatTable, and for reducing the Marks
removeLets :: forall tyname name uni fun a term.
            (term~Term tyname name uni fun a
            ,PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique)
           => Marks
           -> term
           -> (term, FloatTable tyname name uni fun a)
removeLets marks term = runWriter $ go term
  where
    -- TODO: use State for the Marks to safeguard against any bugs where floatable lets are not removed as they should to.
    go :: term -> Writer (FloatTable tyname name uni fun a) term
    go = breakNonRec >>> \case
        -- main operation: for letrec or single letnonrec
        Let a r bs@(representativeBindingUnique -> letU) tIn -> do
            -- go to rhs'es and collect their floattable + cleanedterm
            bs' <- bs & (traversed . bindingSubterms) go
            -- go to inTerm and collect its floattable + cleanedterm
            tIn' <- go tIn
            case M.lookup letU marks of
                -- this is not a floatable let
                Nothing  -> pure $ Let a r bs' tIn'
                -- floatable let found.
                -- move this let to the floattable, and just return the body
                Just pos -> do
                    tell (MM.singleton pos (pure $ BindingGrp a r bs'))
                    pure tIn'

        -- descend and collect
        Apply a t1 t2 -> Apply a <$> go t1 <*> go t2
        TyInst a t ty -> TyInst a <$> go t <*> pure ty
        TyAbs a tyname k t -> TyAbs a tyname k <$> go t
        LamAbs a name ty t -> LamAbs a name ty <$> go t
        IWrap a ty1 ty2 t -> IWrap a ty1 ty2 <$> go t
        Unwrap a t -> Unwrap a <$> go t
        Constr a ty i es -> Constr a ty i <$> traverse go es
        Case a ty arg cs -> Case a ty <$> go arg <*> traverse go cs

        -- no term inside here, nothing to do
        t@Var{} -> pure t
        t@Constant{} -> pure t
        t@Builtin{} -> pure t
        t@Error{} -> pure t

-- | The 3rd and last pass that, given the result of 'removeLets', places the lets back (floats) at the right marked positions.
floatBackLets :: forall tyname name uni fun a term m.
                ( term~Term tyname name uni fun a
                , m~Reader Depth
                , PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique, Semigroup a)
              => term -- ^ the cleanedup, reducted term
              -> FloatTable tyname name uni fun a -- ^ the lets to be floated
              -> term -- ^ the final, floated, and correctly-scoped term
floatBackLets term fTable =
    -- our reader context is only the depth this time.
    flip runReader topDepth $ goTop term
  where

    -- TODO: use State for FloatTable to safeguard against any bugs where floatable-lets were not floated as they should to.
    goTop, go :: term -> m term

    -- after traversing the cleaned term, try to float the lets that are destined for top (global lets)
    goTop = floatLam topUnique <=< go

    go = \case
        -- lam anchor, increase depth & try to float inside the lam's body
        LamAbs a n ty tBody -> local (+1) $
            LamAbs a n ty <$> (floatLam (n^.PLC.theUnique) =<< go tBody)
        -- Lam anchor, increase depth & try to float inside the Lam's body
        TyAbs a n k tBody -> local (+1) $
            TyAbs a n k <$> (floatLam (n^.PLC.theUnique) =<< go tBody)
        -- Unfloatable-let anchor, increase depth
        Let a r bs@(representativeBindingUnique -> letU) tIn -> local (+1) $ do
            -- note that we do not touch the original recursivity of the unfloatable-let
            unfloatableGrp <- BindingGrp a r <$> traverseOf (traversed.bindingSubterms) go bs
            -- rebuild the let-group (we take the minimum bound, i.e. NonRec)
            bindingGrpToLet NonRec
              <$> -- float inside the rhs of the unfloatable group, and merge the bindings
                  floatRhs letU unfloatableGrp
                  -- float right inside the inTerm (similar to lam/Lam)
              <*> (floatLam letU =<< go tIn)

        -- descend
        t                  -> t & termSubterms go

    -- Make a brand new let-group comprised of all the floatable lets just inside the lam-body/Lam-body/let-InTerm
    floatLam :: PLC.Unique -> term -> m term
    floatLam lamU t = do
        herePos <- asks $ \d -> Pos d lamU LamBody
        -- We need to force to Rec because we might merge lets which depend on each other,
        -- but we can't tell because we don't do dependency resolution at this pass.
        -- So we have to be conservative. See Note [LetRec splitting pass]
        floatAt herePos (bindingGrpToLet Rec) t

    floatRhs :: (grp ~ BindingGrp tyname name uni fun a)
             => PLC.Unique
             -> grp -- ^ the unfloatable group
             -> m grp -- ^ the result group extended with the floatable rhs'es (size(result_group) >= size(unfloatable_group))
    floatRhs letU bs = do
        herePos <- asks $ \d -> Pos d letU LetRhs
        -- we don't know from which rhs the floatable-let(s) came from originally,
        -- so we instead are going to semigroup-append the floatable-let bindings together with the unfloatable let-group's bindings
        floatAt herePos (<>) bs

    floatAt :: Pos -- ^ floating position
            -> (BindingGrp tyname name uni fun a -> c -> c) -- ^ how to place the unfloatable-group into the PIR result
            -> c -- ^ term or bindings to float AROUND
            -> m c -- ^ the combined PIR result (terms or bindings)
    floatAt herePos placeIntoFn termOrBindings = do
        -- is there something to be floated here?
        case MM.lookup herePos fTable of
            -- nothing to float, just descend
            Nothing -> pure termOrBindings
            -- all the naked-lets to be floated here
            Just floatableGrps -> do
                -- visit the rhs'es of these floated lets for any potential floatings as well
                -- NOTE: we do not directly run `go(bgGroup)` because that would increase the depth,
                -- and the floated lets are not anchors themselves; instead we run go on the floated-let bindings' subterms.
                floatableGrps' <- floatableGrps & (traversed.bgBindings.traversed.bindingSubterms) go
                -- fold the floatable groups into a *single* floatablegroup and combine that with some pir (term or bindings).
                pure $ fold1 floatableGrps' `placeIntoFn` termOrBindings

-- | The compiler pass of the algorithm (comprised of 3 connected passes).
floatTerm :: (PLC.ToBuiltinMeaning uni fun,
            PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique,
            Ord tyname, Ord name, Semigroup a
            )
          => BuiltinsInfo uni fun -> Term tyname name uni fun a -> Term tyname name uni fun a
floatTerm binfo t =
    mark binfo t
    & flip removeLets t
    & uncurry floatBackLets

-- HELPERS

maxPos :: M.Map k Pos -> Pos
maxPos = foldr max topPos

withDepth :: (r ~ MarkCtx tyname name uni fun, MonadReader r m)
          => (Depth -> Depth) -> m a -> m a
withDepth = local . over markCtxDepth

withLam :: (r ~ MarkCtx tyname name uni fun, MonadReader r m, PLC.HasUnique name unique)
        => name
        -> m a -> m a
withLam (view PLC.theUnique -> u) = local $ \ (MarkCtx d scope binfo vinfo) ->
    let d' = d+1
        pos' = Pos d' u LamBody
    in MarkCtx d' (M.insert u pos' scope) binfo vinfo

withAbs :: (r ~ MarkCtx tyname name uni fun, MonadReader r m, PLC.HasUnique tyname unique)
        => tyname
        -> m a -> m a
withAbs (view PLC.theUnique -> u) = local $ \ (MarkCtx d scope binfo vinfo) ->
    let d' = d+1
        pos' = Pos d' u LamBody
    in MarkCtx d' (M.insert u pos' scope) binfo vinfo

withBs :: (r ~ MarkCtx tyname name uni fun, MonadReader r m, PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique)
       => NE.NonEmpty (Binding tyname name uni fun a3)
       -> Pos
       -> m a -> m a
withBs bs pos = local . over markCtxScope $ \scope ->
    M.fromList [(bid, pos) | bid <- bs^..traversed.bindingIds] <> scope

-- A helper to apply a function iff recursive
ifRec :: Recursivity -> (a -> a) -> a -> a
ifRec r f a = case r of
    Rec    -> f a
    NonRec -> a

floatable
  :: (MonadReader (MarkCtx tyname name uni fun) m, PLC.ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique)
  => BindingGrp tyname name uni fun a
  -> m Bool
floatable (BindingGrp _ _ bs) = do
    binfo <- view markBuiltinsInfo
    vinfo <- view markVarsInfo
    pure $ all (hasNoEffects binfo vinfo) bs
           &&
           -- See Note [Floating type-lets]
           none isTypeBind bs

{-| Returns if a binding has absolutely no effects  (see Value.hs)
See Note [Purity, strictness, and variables]
An extreme alternative implementation is to treat *all strict* bindings as unfloatable, e.g.:
`hasNoEffects = \case {TermBind _ Strict _  _ -> False; _ -> True}`
-}
hasNoEffects
    :: (PLC.ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique)
    => BuiltinsInfo uni fun
    -> VarsInfo tyname name
    -> Binding tyname name uni fun a -> Bool
hasNoEffects binfo vinfo = \case
    TypeBind{}               -> True
    DatatypeBind{}           -> True
    TermBind _ NonStrict _ _ -> True
    -- have to check for purity
    TermBind _ Strict _ t    -> isPure binfo vinfo t

isTypeBind :: Binding tyname name uni fun a -> Bool
isTypeBind = \case TypeBind{} -> True; _ -> False

-- | Breaks down linear let nonrecs by
-- the rule: {let nonrec (b:bs) in t} === {let nonrec b in let nonrec bs in t}
breakNonRec :: Term tyname name uni fun a -> Term tyname name uni fun a
breakNonRec = \case
    Let a NonRec (NE.uncons -> (b, Just bs)) tIn  ->
      (Let a NonRec (pure b) $ Let a NonRec bs tIn)
    t -> t

{- Note [Floating rhs-nested lets]

A nested let inside a let-rhs that depends on that rhs is for example:

let rec parent = (let (rec|nonrec) child = parent in ...)  in ...
OR
let rec grandparent = (let rec parent = (let (rec|nonrec) child = grandparent in ...) in ...) in ...

If such a child is floatable and its calculated float marker (maximum position)
is another let's position (e.g. parent or grandparent),
we have to float right inside the let-rhs and not right inside the let-interm.
However we lost the information in which specific rhs from the group of rhse's)of the (grand)parent let-group,
the dependent let came from.

Squeezing with such a parent, unfloatable let means that the parent let *must* be recursive.
Since the child let is depending on the parent let --- uses some parent-introduced variable(s) ---,
it is implied that the parent was originally rec, to begin with; we do not touch the original recursivity of an unfloatable let.

Note about squeezing order:
(floatable<>unfloatable) VERSUS (unfloatable<>floatable) does not matter, because it does not change the meaning.

The end result is that no nested, floatable let will appear anymore inside another let's rhs at the algorithm's output,
(e.g. invalid output:  let x=1+(let y=3 in y) in ...)
*EXCEPT* if the nested let is intercepted by a lam/Lam anchor (depends on a lam/Lam that is located inside the parent-let's rhs)
e.g. valid output: let x= \z -> (let y = 3+z in y) in ...
-}

{- Note [Floating type-lets]

In general, type-lets cannot be floated because of opaqueness. For example, it is unsound to turn

(let a = x in \(b : a) t) (y : x)

into

let a = x in (\(b : a) t) (y : x)

Because type-lets are opaque, this doesn't type check - the formal parameter has type `a` while
`y` has type `x`.
-}
