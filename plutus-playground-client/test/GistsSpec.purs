module GistsTests
       ( all
       ) where

import Prelude

import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Data.Either (Either(..))
import Gist (GistId(..))
import Gists (parseGistUrl)
import Node.FS (FS)
import Test.Unit (TestSuite, suite, test)
import TestUtils (equalGShow)

all :: forall eff. TestSuite (exception :: EXCEPTION, fs :: FS, random :: RANDOM | eff)
all =
  suite "Gists" do
    parseGistUrlTests

parseGistUrlTests :: forall eff. TestSuite eff
parseGistUrlTests =
  suite "parseGistUrlTests" do
    let gistId = GistId "9d8feacacd8c4b553f870c4448483938"
    test "Ref" $ equalGShow (Right gistId) (parseGistUrl "9d8feacacd8c4b553f870c4448483938")
    test "Direct link" $ equalGShow (Right gistId) (parseGistUrl "https://gist.github.com/9d8feacacd8c4b553f870c4448483938")
    test "User link" $ equalGShow (Right gistId) (parseGistUrl "https://gist.github.com/krisajenkins/9d8feacacd8c4b553f870c4448483938")
    test "No ID" $ equalGShow (Left "Could not parse Gist Url") (parseGistUrl "https://gist.github.com/")
    test "Too long" $ equalGShow (Left  "Could not parse Gist Url") (parseGistUrl "aaaabbbbccccddddeeeeffff000011112")
