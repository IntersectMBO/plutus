{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module PlutusCore.Generators.QuickCheck.Utils
  ( module PlutusCore.Generators.QuickCheck.Utils
  , module Export
  ) where

import PlutusCore.Default
import PlutusCore.Generators.QuickCheck.Split as Export
import PlutusCore.MkPlc hiding (error)
import PlutusCore.Name.Unique
import PlutusCore.Pretty
import PlutusCore.Quote
import PlutusIR
import PlutusIR.Compiler.Datatype
import PlutusIR.Subst

import Data.Kind qualified as GHC
import Data.List.NonEmpty (NonEmpty (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Set.Lens (setOf)
import Data.String
import Prettyprinter
import Test.QuickCheck

{-| Generate a list of the given length, all arguments of which are distinct. Takes O(n^2) time
or more if the generator is likely to generate equal values. -}
uniqueVectorOf :: Eq a => Int -> Gen a -> Gen [a]
uniqueVectorOf i0 genX = go [] i0
  where
    go acc i
      | i <= 0 = pure acc
      | otherwise = do
          x <- genX `suchThat` (`notElem` acc)
          go (x : acc) (i - 1)

-- | Show a `Doc` when a property fails.
ceDoc :: Testable t => Doc ann -> t -> Property
ceDoc d = counterexample (render d)

{-| Bind a value to a name in a property so that
it is displayed as a `name = thing` binding if the
property fails. -}
letCE
  :: (PrettyReadable a, Testable p)
  => String
  -> a
  -> (a -> p)
  -> Property
letCE name x k = ceDoc (fromString name <+> "=" <+> prettyReadable x) (k x)

{-| Like `forAllShrink` but displays the bound value as
a named pretty-printed binding like `letCE` -}
forAllDoc
  :: (PrettyReadable a, Testable p)
  => String
  -> Gen a
  -> (a -> [a])
  -> (a -> p)
  -> Property
forAllDoc name g shr k =
  forAllShrinkBlind g shr $ \x ->
    ceDoc
      (fromString name <+> "=" <+> prettyReadable x)
      (k x)

{-| Check that a list of potential counterexamples is empty and display the
list as a QuickCheck counterexample if its not. -}
assertNoCounterexamples :: PrettyReadable a => [a] -> Property
assertNoCounterexamples [] = property True
assertNoCounterexamples bad = ceDoc (prettyReadable bad) False

-- * Containers (zipper-ish, very useful for shrinking).

-- There's https://hackage.haskell.org/package/functor-combo-0.3.6/docs/FunctorCombo-Holey.html
-- (explained in http://conal.net/blog/posts/differentiation-of-higher-order-types), but it's kinda
-- easier to roll out our own version than to dig through the generics in that library. Plus, the
-- library has multiple interfaces looking slightly different and it's not immediately clear how
-- they relate to each other.
-- | A type is a container for the purposes of shrinking if it has:
class Container f where
  data OneHoleContext f :: GHC.Type -> GHC.Type
  -- ^ One hole context where we can shrink a single "element" of the container

  oneHoleContexts :: f a -> [(OneHoleContext f a, a)]
  -- ^ A way of getting all the one hole contexts of an `f a`

  plugHole :: OneHoleContext f a -> a -> f a
  -- ^ A way to plug the hole with a new, shrunk, term

-- | Containers for lists is zipper like, a hole is a specific position in the list
instance Container [] where
  data OneHoleContext [] a = ListContext [a] [a]

  oneHoleContexts [] = []
  oneHoleContexts (x : xs) =
    (ListContext [] xs, x)
      : [ (ListContext (x : ys) zs, y)
        | (ListContext ys zs, y) <- oneHoleContexts xs
        ]

  plugHole (ListContext xs ys) z = xs ++ [z] ++ ys

-- | An analogous implementation of `Container` as for lists
instance Container NonEmpty where
  data OneHoleContext NonEmpty a = NonEmptyContext [a] [a]

  oneHoleContexts (x :| xs) =
    (NonEmptyContext [] xs, x)
      : [ (NonEmptyContext (x : ys) zs, y)
        | (ListContext ys zs, y) <- oneHoleContexts xs
        ]

  plugHole (NonEmptyContext [] ys) z = z :| ys
  plugHole (NonEmptyContext (x : xs) ys) z = x :| xs ++ [z] ++ ys

-- Note that this doesn't have any relation to 'freshenTyName'. Both functions change the unique,
-- but do it in incomparably different ways.
-- | Freshen a TyName so that it does not equal any of the names in the set.
freshenTyNameWith :: Set TyName -> TyName -> TyName
freshenTyNameWith fvs (TyName (Name x j)) = TyName (Name x i)
  where
    i = succ $ Set.findMax is
    is = Set.insert j $ Set.insert (toEnum 0) $ Set.mapMonotonic (_nameUnique . unTyName) fvs

maxUsedUnique :: Set TyName -> Unique
maxUsedUnique fvs = i
  where
    i = Set.findMax is
    is = Set.insert (toEnum 0) $ Set.mapMonotonic (_nameUnique . unTyName) fvs

-- | Get the names and types of the constructors of a datatype.
constrTypes :: Datatype TyName Name DefaultUni () -> [(Name, Type TyName DefaultUni ())]
constrTypes (Datatype _ _ xs _ cs) = [(c, mkIterTyForall xs ty) | VarDecl _ c ty <- cs]

-- | Get the name and type of the match function for a given datatype.
matchType :: Datatype TyName Name DefaultUni () -> (Name, Type TyName DefaultUni ())
matchType d@(Datatype _ (TyVarDecl _ a _) xs m cs) = (m, destrTy)
  where
    fvs =
      Set.fromList (a : [x | TyVarDecl _ x _ <- xs])
        <> mconcat [setOf ftvTy ty | VarDecl _ _ ty <- cs]
    maxUsed = maxUsedUnique fvs
    destrTy = runQuote $ markNonFresh maxUsed >> mkDestructorTy d
