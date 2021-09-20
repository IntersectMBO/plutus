module CursorTests
  ( all
  ) where

import Prelude
import Cursor (Cursor)
import Cursor as Cursor
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (over, preview)
import Data.Lens.Index (ix)
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.NonEmpty (NonEmpty(NonEmpty))
import Data.String.Extra (unlines)
import Data.Tuple (Tuple(..))
import Test.QuickCheck (class Arbitrary, arbitrary, withHelp, (<?>), (===))
import Test.QuickCheck.Gen (Gen, arrayOf, elements)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Test.Unit.QuickCheck (quickCheck)
import TestUtils (genIndex, genLooseIndex)

data Operation
  = Set Int
  | Left
  | Right
  | First
  | Last

derive instance genericOperation :: Generic Operation _

instance showOperation :: Show Operation where
  show = genericShow

applyOperation :: forall a. Operation -> Cursor a -> Cursor a
applyOperation (Set index) = Cursor.setIndex index

applyOperation Left = Cursor.left

applyOperation Right = Cursor.right

applyOperation First = Cursor.first

applyOperation Last = Cursor.last

genOperation :: forall a. Cursor a -> Gen Operation
genOperation cursor = do
  index <- genLooseIndex cursor
  elements (NonEmpty (Set index) [ Left, Right ])

data Scenario a
  = Scenario (Cursor a) (Array Operation)

genScenario :: forall a. Arbitrary a => Gen (Scenario a)
genScenario = do
  cursor <- Cursor.fromArray <$> arrayOf arbitrary
  operations <- arrayOf $ genOperation cursor
  pure $ Scenario cursor operations

------------------------------------------------------------
all :: TestSuite
all =
  suite "Cursor" do
    operationsTests
    lensTests
    snocTests
    mapWithIndexTests
    deleteAtTests

operationsTests :: TestSuite
operationsTests =
  test "Operations are safe." do
    quickCheck do
      Scenario cursor operations <- genScenario :: Gen (Scenario String)
      let
        finalCursor = Array.foldr applyOperation cursor operations
      pure
        $ withHelp
            (isJust (Cursor.current finalCursor) || (Cursor.null finalCursor))
            ("Invalid state with cursor: " <> show cursor <> " and operations: " <> show operations)

lensTests :: TestSuite
lensTests =
  test "Lens indexing works." do
    quickCheck do
      cursor <- arbitrary :: Gen (Cursor String)
      let
        fromGetter = Cursor.current cursor

        fromLens = preview (Cursor._current) cursor
      pure $ fromGetter == fromLens
        <?> unlines
            [ "Invalid lookup from cursor: " <> show cursor
            , "Current returns: " <> show fromGetter
            , "Lens returns: " <> show fromLens
            ]
    equal
      (Cursor.fromArray [ 1, 4, 3 ])
      (over (ix 1) ((*) 2) (Cursor.fromArray [ 1, 2, 3 ]))

snocTests :: TestSuite
snocTests =
  test "snoc appends a new value to the end of the cursor." do
    quickCheck do
      x <- arbitrary :: Gen String
      cursor <- arbitrary
      pure $ Just x === Cursor.current (Cursor.snoc cursor x)

mapWithIndexTests :: TestSuite
mapWithIndexTests =
  test "mapWithIndex works" do
    equal
      (Cursor.fromArray [ 1 + 0, 3 + 1, 5 + 2, 7 + 3, 11 + 4 ])
      (Cursor.mapWithIndex (+) (Cursor.fromArray [ 1, 3, 5, 7, 11 ]))
    quickCheck \cursor ->
      Cursor.toArray (Cursor.mapWithIndex (+) cursor)
        === Array.mapWithIndex (+) (Cursor.toArray cursor)

deleteAtTests :: TestSuite
deleteAtTests =
  suite "deleteAt" do
    test "deleteAt amends the contents correctly." do
      quickCheck do
        cursor <- arbitrary :: Gen (Cursor String)
        index <- genIndex cursor
        let
          deleted = Cursor.deleteAt index cursor
        pure
          $ Cursor.toArray (Cursor.deleteAt index cursor)
          === fromMaybe
              (Cursor.toArray cursor)
              (Array.deleteAt index (Cursor.toArray cursor))
    test "deleteAt preserves the cursor position." do
      quickCheck do
        cursor <- arbitrary :: Gen (Cursor Int)
        index <- genIndex cursor
        let
          deleted = Cursor.deleteAt index cursor
        pure
          $ if Cursor.length cursor < 2 then
              Cursor.current deleted == Nothing
                <?> "A cursor will be empty if we delete its only element: "
                <> show (Tuple index cursor)
            else
              if Cursor.getIndex cursor == index then
                if Cursor.getIndex cursor == Cursor.length cursor - 1 then
                  Cursor.current (Cursor.left cursor) == Cursor.current deleted
                    <?> unlines
                        [ "Deleting an element at the cursor's position should shift left:"
                        , "Index: " <> show index
                        , "Cursor: " <> show cursor
                        , "Deleted: " <> show deleted
                        , "Cursor current: " <> show (Cursor.current (Cursor.left cursor))
                        , "Deleted current: " <> show (Cursor.current deleted)
                        ]
                else
                  Cursor.current (Cursor.right cursor) == Cursor.current deleted
                    <?> unlines
                        [ "Deleting an element at the cursor's position should shift right:"
                        , "Index: " <> show index
                        , "Cursor: " <> show cursor
                        , "Deleted: " <> show deleted
                        , "Cursor current: " <> show (Cursor.current (Cursor.right cursor))
                        , "Deleted current: " <> show (Cursor.current deleted)
                        ]
              else
                Cursor.current cursor == Cursor.current deleted
                  <?> "Deleting an element that isn't at the cursor's position should not affect the current target: "
                  <> show (Tuple index cursor)
