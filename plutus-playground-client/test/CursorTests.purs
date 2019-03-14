module CursorTests
       ( all
       ) where

import Prelude

import Control.Monad.Eff.Random (RANDOM)
import Control.Monad.Gen (chooseInt)
import Control.Monad.Gen.Class (class MonadGen)
import Cursor (Cursor)
import Cursor as Cursor
import Data.Array as Array
import Data.Generic (class Generic, gShow)
import Data.Lens (over, preview)
import Data.Lens.Index (ix)
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.NonEmpty (NonEmpty(NonEmpty))
import Data.Tuple (Tuple(..))
import Test.QuickCheck (class Arbitrary, class Testable, arbitrary, withHelp, (<?>))
import Test.QuickCheck.Gen (Gen, arrayOf, elements)
import Test.Unit (TestSuite, Test, suite, test)
import Test.Unit.Assert (equal)
import Test.Unit.QuickCheck (quickCheck)

data Operation
  = Set Int
  | Left
  | Right
  | First
  | Last

derive instance genericOperation :: Generic Operation

instance showOperation :: Show Operation where
  show = gShow

applyOperation :: forall a. Operation -> Cursor a -> Cursor a
applyOperation (Set index) = Cursor.setIndex index
applyOperation Left = Cursor.left
applyOperation Right = Cursor.right
applyOperation First = Cursor.first
applyOperation Last = Cursor.last

genIndex :: forall m a. MonadGen m => Cursor a -> m Int
genIndex cursor = chooseInt 0 (Cursor.length cursor - 1)

-- | Generate an index which is roughly in range, but may be slightly out of bounds.
genLooseIndex :: forall m a. MonadGen m => Cursor a -> m Int
genLooseIndex cursor = chooseInt (-5) (Cursor.length cursor + 5)

genOperation :: forall a. Cursor a -> Gen Operation
genOperation cursor = do
  index <- genLooseIndex cursor
  elements (NonEmpty (Set index) [ Left, Right ])

data Scenario a = Scenario (Cursor a) (Array Operation)

genScenario :: forall a. Arbitrary a => Gen (Scenario a)
genScenario = do
  cursor <- Cursor.fromArray <$> arrayOf arbitrary
  operations <- arrayOf $ genOperation cursor
  pure $ Scenario cursor operations

------------------------------------------------------------

all :: forall aff. TestSuite (random :: RANDOM | aff)
all =
  suite "Cursor" do
    operationsTests
    lensTests
    snocTests
    mapWithIndexTests
    deleteAtTests

operationsTests :: forall eff. TestSuite (random :: RANDOM | eff)
operationsTests =
  test "Operations are safe." do
    quickCheck do
      Scenario cursor operations <- genScenario :: Gen (Scenario String)
      let finalCursor = Array.foldr applyOperation cursor operations
      pure $ withHelp
          (isJust (Cursor.current finalCursor) || (Cursor.null finalCursor))
          ("Invalid state with cursor: " <> show cursor <> " and operations: " <> show operations)

lensTests :: forall eff. TestSuite (random :: RANDOM | eff)
lensTests =
  test "Lens indexing works." do
    quickCheck do
      cursor <- arbitrary :: Gen (Cursor String)
      let fromGetter = Cursor.current cursor
          fromLens = preview (Cursor._current) cursor
      pure $ fromGetter == fromLens
             <?> ("Invalid lookup from cursor: " <> show cursor
                  <> "\nCurrent returns: " <> show fromGetter
                  <> "\nLens returns: " <> show fromLens)

    equal
      (Cursor.fromArray [1,4,3])
      (over (ix 1) ((*) 2) (Cursor.fromArray [1,2,3]))

snocTests :: forall eff. TestSuite (random :: RANDOM | eff)
snocTests =
  test "snoc appends a new value to the end of the cursor." do
    quickCheck do
      x <- arbitrary :: Gen String
      cursor <- arbitrary
      pure $ Just x == Cursor.current (Cursor.snoc cursor x)

mapWithIndexTests :: forall eff. TestSuite (random :: RANDOM | eff)
mapWithIndexTests =
  test "mapWithIndex works" do
    equal
      (Cursor.fromArray [1+0,3+1,5+2,7+3,11+4])
      (Cursor.mapWithIndex (+) (Cursor.fromArray [1,3,5,7,11]))

    quickCheck \cursor -> Cursor.toArray (Cursor.mapWithIndex (+) cursor)
                          ==
                          Array.mapWithIndex (+) (Cursor.toArray cursor)

deleteAtTests :: forall eff. TestSuite (random :: RANDOM | eff)
deleteAtTests =
  suite "deleteAt" do
    test "deleteAt amends the contents correctly." do
      quickCheck do
        cursor <- arbitrary :: Gen (Cursor String)
        index <- genIndex cursor
        let deleted = Cursor.deleteAt index cursor
        pure $
          Cursor.toArray (Cursor.deleteAt index cursor)
          ==
          fromMaybe
            (Cursor.toArray cursor)
            (Array.deleteAt index (Cursor.toArray cursor))

    test "deleteAt preserves the cursor position." do
      quickCheck do
        cursor <- arbitrary :: Gen (Cursor Int)
        index <- genIndex cursor
        let deleted = Cursor.deleteAt index cursor
        pure $
          if Cursor.length cursor < 2
          then Cursor.current deleted == Nothing
                 <?> "A cursor will be empty if we delete its only element: " <> show (Tuple index cursor)
          else if Cursor.getIndex cursor == index
               then if Cursor.getIndex cursor == Cursor.length cursor - 1
                    then Cursor.current (Cursor.left cursor) == Cursor.current deleted
                      <?> "Deleting an element at the cursor's position should shift left:"
                             <> "\nIndex: " <> show index
                             <> "\nCursor: " <> show cursor
                             <> "\nDeleted: " <> show deleted
                             <> "\nCursor current: " <> show (Cursor.current (Cursor.left cursor))
                             <> "\nDeleted current: " <> show (Cursor.current deleted)
                    else Cursor.current (Cursor.right cursor) == Cursor.current deleted
                      <?> "Deleting an element at the cursor's position should shift right:"
                             <> "\nIndex: " <> show index
                             <> "\nCursor: " <> show cursor
                             <> "\nDeleted: " <> show deleted
                             <> "\nCursor current: " <> show (Cursor.current (Cursor.right cursor))
                             <> "\nDeleted current: " <> show (Cursor.current deleted)
          else Cursor.current cursor == Cursor.current deleted
                 <?> "Deleting an element that isn't at the cursor's position should not affect the current target: " <> show (Tuple index cursor)
