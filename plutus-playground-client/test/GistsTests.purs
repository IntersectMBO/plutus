module GistsTests
  ( all
  ) where

import Prelude
import Data.Either (Either(..))
import Data.Generic.Rep.Show (genericShow)
import Gist (GistId(..))
import Gists.Types (parseGistUrl)
import Test.Unit (TestSuite, Test, suite, test)
import TestUtils (equalWithBiformatter)

all :: TestSuite
all =
  suite "Gists" do
    parseGistUrlTests

parseGistUrlTests :: TestSuite
parseGistUrlTests =
  suite "parseGistUrlTests" do
    let
      gistId = GistId "9d8feacacd8c4b553f870c4448483938"
    test "Ref" $ equalGistResult (Right gistId) (parseGistUrl "9d8feacacd8c4b553f870c4448483938")
    test "Direct link" $ equalGistResult (Right gistId) (parseGistUrl "https://gist.github.com/9d8feacacd8c4b553f870c4448483938")
    test "User link" $ equalGistResult (Right gistId) (parseGistUrl "https://gist.github.com/krisajenkins/9d8feacacd8c4b553f870c4448483938")
    test "No ID" $ equalGistResult (Left "Could not parse Gist Url") (parseGistUrl "https://gist.github.com/")
    test "Too long" $ equalGistResult (Left "Could not parse Gist Url") (parseGistUrl "aaaabbbbccccddddeeeeffff000011112")

equalGistResult :: Either String GistId -> Either String GistId -> Test
equalGistResult = equalWithBiformatter identity genericShow
