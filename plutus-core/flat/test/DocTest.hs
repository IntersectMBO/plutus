
-- Execute doctest tests with no dependencies on doctest
-- TODO: move in a different doctest-static package
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}
-- move to doctest
module PlutusCore.Flat.Test.DocTest
  ( asPrint
  , test
  , testProp
  , LineChunk(..)
  , ExpectedLine(..)
  )
where
import Data.Text qualified as T
import Test.Tasty
import Test.Tasty.HUnit

import Test.Tasty.QuickCheck
-- import           Runner.Example
import Data.Char
import Data.List
import Data.String

class Print f where
    asPrint :: f -> IO String

instance Show a => Print (IO a) where
  asPrint io = io >>= return . show

instance {-# OVERLAPPABLE #-} Show a => Print a where
  asPrint a = return (show a)

{-

-}
-- test :: TestName -> ExpectedResult -> IO String -> IO TestTree
test :: TestName -> String -> IO String -> IO TestTree
test loc expectedS valIO = do
  let expected = read expectedS
  actual <- lines <$> valIO
  return $ testCase loc (mkResult expected actual @=? Equal)
  -- return $ testCase loc (unlines exp @=? unlines actual)

testProp :: Testable t => TestName -> t -> IO TestTree
testProp loc = return . testProperty loc


-- Code copied and adapted by doctest

data Result = Equal | NotEqual [String]
  deriving (Eq, Show,Read)

-- | Remove trailing white space from a string.
--
-- >>> stripEnd "foo   "
-- "foo"
stripEnd :: String -> String
stripEnd = reverse . dropWhile isSpace . reverse

mkResult :: ExpectedResult -> [String] -> Result
mkResult expected actual | expected `matches` actual = Equal
                         | otherwise = NotEqual (formatNotEqual expected actual)
 where
  chunksMatch :: [LineChunk] -> String -> Bool
  chunksMatch []             "" = True
  chunksMatch [LineChunk xs] ys = stripEnd xs == stripEnd ys
  chunksMatch (LineChunk x : xs) ys =
    x `isPrefixOf` ys && xs `chunksMatch` drop (length x) ys
  chunksMatch zs@(WildCardChunk : xs) (_ : ys) =
    xs `chunksMatch` ys || zs `chunksMatch` ys
  chunksMatch _ _ = False

  matches :: ExpectedResult -> [String] -> Bool
  matches (ExpectedLine x : xs) (y : ys) = x `chunksMatch` y && xs `matches` ys
  matches (WildCardLine : xs) ys | xs `matches` ys = True
  matches zs@(WildCardLine : _) (_ : ys)           = zs `matches` ys
  matches []                    []                 = True
  matches []                    _                  = False
  matches _                     []                 = False


formatNotEqual :: ExpectedResult -> [String] -> [String]
formatNotEqual expected_ actual =
  formatLines "expected: " expected ++ formatLines " but got: " actual
 where
  expected :: [String]
  expected = map
    (\x -> case x of
      ExpectedLine str -> concatMap lineChunkToString str
      WildCardLine     -> "..."
    )
    expected_

  -- use show to escape special characters in output lines if any output line
  -- contains any unsafe character
  escapeOutput | any (not . isSafe) (concat $ expected ++ actual) = map show
               | otherwise = id

  isSafe :: Char -> Bool
  isSafe c = c == ' ' || (isPrint c && (not . isSpace) c)

  formatLines :: String -> [String] -> [String]
  formatLines message xs = case escapeOutput xs of
    y : ys -> (message ++ y) : map (padding ++) ys
    []     -> [message]
    where padding = replicate (length message) ' '

lineChunkToString :: LineChunk -> String
lineChunkToString WildCardChunk   = "..."
lineChunkToString (LineChunk str) = str

-- import           Control.DeepSeq (deepseq, NFData(rnf))

-- | A thing with a location attached.
data Located a = Located Location a
  deriving (Eq, Show, Functor)

-- instance NFData a => NFData (Located a) where
--   rnf (Located loc a) = loc `deepseq` a `deepseq` ()

-- | Discard location information.
unLoc :: Located a -> a
unLoc (Located _ a) = a

-- | Add dummy location information.
noLocation :: a -> Located a
noLocation = Located (UnhelpfulLocation "<no location info>")

-- | A line number.
type Line = Int

-- | A combination of file name and line number.
data Location = UnhelpfulLocation String | Location FilePath Line
  deriving Eq

instance Show Location where
  show (UnhelpfulLocation s) = s
  show (Location file line ) = file ++ ":" ++ show line

-- instance NFData Location where
--   rnf (UnhelpfulLocation str) = str `deepseq` ()
--   rnf (Location file line   ) = file `deepseq` line `deepseq` ()

-- |
-- Create a list from a location, by repeatedly increasing the line number by
-- one.
enumerate :: Location -> [Location]
enumerate loc = case loc of
  UnhelpfulLocation _ -> repeat loc
  Location file line  -> map (Location file) [line ..]

data DocTest = Example Expression ExpectedResult | Property Expression
  deriving (Eq, Show,Read)

data LineChunk = LineChunk String | WildCardChunk
  deriving (Show, Eq,Read)

instance IsString LineChunk where
  fromString = LineChunk

data ExpectedLine = ExpectedLine [LineChunk] | WildCardLine
  deriving (Show, Eq,Read)

instance IsString ExpectedLine where
  fromString = ExpectedLine . return . LineChunk

type Expression = String
type ExpectedResult = [ExpectedLine]
