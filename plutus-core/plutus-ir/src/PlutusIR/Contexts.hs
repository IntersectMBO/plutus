{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

{-| Datatypes representing 'contexts with holes' in Plutus IR terms.

Useful for focussing on a sub-part of a term and then reconstructing the term, but
with the context as a reified datatype that can be inspected and modified. -}
module PlutusIR.Contexts where

import Control.Lens
import Data.DList qualified as DList
import Data.Functor (void)
import PlutusCore.Arity
import PlutusCore.Name.Unique qualified as PLC
import PlutusIR.Analysis.VarInfo
import PlutusIR.Core
import PlutusIR.MkPir

{-| A context for an iterated term/type application, with the hole at the head of the
application. -}
data AppContext tyname name uni fun ann
  = TermAppContext (Term tyname name uni fun ann) ann (AppContext tyname name uni fun ann)
  | TypeAppContext (Type tyname uni ann) ann (AppContext tyname name uni fun ann)
  | AppContextEnd

{-| Takes a term and views it as a head plus an 'AppContext', e.g.

@
    [{ f t } u v]
    -->
    (f, [{ _ t } u v])
    ==
    f (TypeAppContext t (TermAppContext u (TermAppContext v AppContextEnd)))
@ -}
splitApplication
  :: Term tyname name uni fun ann
  -> (Term tyname name uni fun ann, AppContext tyname name uni fun ann)
splitApplication tm =
  go tm AppContextEnd
  where
    go (Apply ann f arg) ctx = go f (TermAppContext arg ann ctx)
    go (TyInst ann f tyArg) ctx = go f (TypeAppContext tyArg ann ctx)
    go t ctx = (t, ctx)

-- | Fills in the hole in an 'AppContext', the inverse of 'splitApplication'.
fillAppContext
  :: Term tyname name uni fun ann
  -> AppContext tyname name uni fun ann
  -> Term tyname name uni fun ann
fillAppContext t = \case
  AppContextEnd -> t
  TermAppContext arg ann ctx -> fillAppContext (Apply ann t arg) ctx
  TypeAppContext tyArg ann ctx -> fillAppContext (TyInst ann t tyArg) ctx

dropAppContext :: Int -> AppContext tyname name uni fun a -> AppContext tyname name uni fun a
dropAppContext i ctx | i <= 0 = ctx
dropAppContext i ctx = case ctx of
  AppContextEnd -> ctx
  TermAppContext _ _ ctx' -> dropAppContext (i - 1) ctx'
  TypeAppContext _ _ ctx' -> dropAppContext (i - 1) ctx'

lengthContext :: AppContext tyname name uni fun a -> Int
lengthContext = go 0
  where
    go acc = \case
      AppContextEnd -> acc
      TermAppContext _ _ ctx -> go (acc + 1) ctx
      TypeAppContext _ _ ctx -> go (acc + 1) ctx

splitAppContext
  :: Int
  -> AppContext tyname name uni fun a
  -> (AppContext tyname name uni fun a, AppContext tyname name uni fun a)
splitAppContext = go id
  where
    go
      :: (AppContext tyname name uni fun a -> AppContext tyname name uni fun a)
      -> Int
      -> AppContext tyname name uni fun a
      -> (AppContext tyname name uni fun a, AppContext tyname name uni fun a)
    go acc i ctx | i <= 0 = (acc AppContextEnd, ctx)
    go acc i ctx = case ctx of
      c@AppContextEnd -> (acc c, AppContextEnd)
      TermAppContext arg ann ctx' -> go (\end -> acc $ TermAppContext arg ann end) (i - 1) ctx'
      TypeAppContext arg ann ctx' -> go (\end -> acc $ TypeAppContext arg ann end) (i - 1) ctx'

appendAppContext
  :: AppContext tyname name uni fun a
  -> AppContext tyname name uni fun a
  -> AppContext tyname name uni fun a
appendAppContext ctx1 ctx2 = go ctx1
  where
    go AppContextEnd = ctx2
    go (TermAppContext arg ann ctx') = TermAppContext arg ann $ go ctx'
    go (TypeAppContext arg ann ctx') = TypeAppContext arg ann $ go ctx'

instance Semigroup (AppContext tyname name uni fun a) where
  (<>) = appendAppContext

instance Monoid (AppContext tyname name uni fun a) where
  mempty = AppContextEnd

data Saturation = Oversaturated | Undersaturated | Saturated

-- | Do the given arguments saturate the given arity?
saturates :: AppContext tyname name uni fun a -> Arity -> Maybe Saturation
-- Exactly right
saturates AppContextEnd [] = Just Saturated
-- Parameters left - undersaturated
saturates AppContextEnd _ = Just Undersaturated
-- Match a term parameter to a term arg
saturates (TermAppContext _ _ ctx) (TermParam : arities) = saturates ctx arities
-- Match a type parameter to a type arg
saturates (TypeAppContext _ _ ctx) (TypeParam : arities) = saturates ctx arities
-- Param/arg mismatch
saturates (TermAppContext {}) (TypeParam : _) = Nothing
saturates (TypeAppContext {}) (TermParam : _) = Nothing
-- Arguments left - undersaturated
saturates (TermAppContext {}) [] = Just Oversaturated
saturates (TypeAppContext {}) [] = Just Oversaturated

{-| A split up version of the 'AppContext' for a datatype match, with the various
parts we might want to look at.

We have this datatype to make it easier to abstract over different ways that
a match might be constructed at the term level. For example, some builtin
"matchers" have the arguments in a different order to the matchers from normal
PIR datatypes. -}
data SplitMatchContext tyname name uni fun a = SplitMatchContext
  { smTyVars :: AppContext tyname name uni fun a
  , smScrutinee :: (Term tyname name uni fun a, Type tyname uni (), a)
  , smResTy :: (Type tyname uni a, a)
  , smBranches :: AppContext tyname name uni fun a
  }

{-| Extract the type application arguments from an 'AppContext'.
Returns 'Nothing' if the context contains a TermAppContext.
See 'test_extractTyArgs' -}
extractTyArgs :: AppContext tyname name uni fun a -> Maybe [Type tyname uni a]
extractTyArgs = go DList.empty
  where
    go acc = \case
      TypeAppContext ty _ann ctx -> go (DList.snoc acc ty) ctx
      TermAppContext {} -> Nothing
      AppContextEnd -> Just (DList.toList acc)

-- | Split a normal datatype 'match'.
splitNormalDatatypeMatch
  :: (PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique)
  => VarsInfo tyname name uni a
  -> name
  -> AppContext tyname name uni fun a
  -> Maybe (SplitMatchContext tyname name uni fun a)
splitNormalDatatypeMatch vinfo matcherName args
  | Just dmInfo@(DatatypeMatcher dmParentTyname) <- lookupVarInfo matcherName vinfo
  , -- Needs to be saturated otherwise we won't find the bits!
    Just dmArity <- varInfoArity dmInfo vinfo
  , Just Saturated <- saturates args dmArity
  , Just (DatatypeTyVar (Datatype _ tyname tyvars _ _)) <- lookupTyVarInfo dmParentTyname vinfo
  , -- Split up the application into:
    -- 1. The initial datatype type instantiations
    -- 2. The scrutinee
    -- 3. The result type variable instantiation
    -- 4. The branches
    (vars, TermAppContext scrut scrutAnn (TypeAppContext resTy resTyAnn branches)) <-
      splitAppContext (length tyvars) args
  , Just tvs <- extractTyArgs vars =
      let
        scrutTy = mkIterTyApp (mkTyVar () (void tyname)) $ ((),) . void <$> tvs
        sm = SplitMatchContext vars (scrut, scrutTy, scrutAnn) (resTy, resTyAnn) branches
       in
        Just sm
  | otherwise = Nothing

-- | Reconstruct a normal datatype 'match'.
reconstructNormalDatatypeMatch
  :: SplitMatchContext tyname name uni fun a
  -> AppContext tyname name uni fun a
reconstructNormalDatatypeMatch
  (SplitMatchContext vars (scrut, _, scrutAnn) (resTy, resTyAnn) branches) =
    vars <> TermAppContext scrut scrutAnn (TypeAppContext resTy resTyAnn branches)

-- | Split a normal datatype 'match'.
asNormalDatatypeMatch
  :: (PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique)
  => VarsInfo tyname name uni a
  -> name
  -> Prism' (AppContext tyname name uni fun a) (SplitMatchContext tyname name uni fun a)
asNormalDatatypeMatch vinfo name =
  prism
    reconstructNormalDatatypeMatch
    ( \args -> case splitNormalDatatypeMatch vinfo name args of
        Just sm -> Right sm
        Nothing -> Left args
    )

{- Note [Context splitting in a recursive pass]
When writing a recursive pass that processes the whole program, you must be
a bit cautious when using a context split. The context split may traverse
part of the program, which will _also_ be traversed by the main recursive
traversal. This can lead to quadratic runtime.

This is usually okay for something like 'splitApplication', since it is
quadratic in the longest application in the program, which is usually not
significantly long.
-}
