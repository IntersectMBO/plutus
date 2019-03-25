module GistsTests
       ( all
       ) where

import Prelude

import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Data.Either (Either(..))
import Data.Generic (gShow)
import Gist (GistId(..))
import Gists (parseGistUrl)
import Node.FS (FS)
import Test.Unit (TestSuite, Test, failure, success, suite, test)

all :: forall eff. TestSuite (exception :: EXCEPTION, fs :: FS, random :: RANDOM | eff)
all =
  suite "Gists" do
    parseGistUrlTests

parseGistUrlTests :: forall eff. TestSuite eff
parseGistUrlTests =
  suite "parseGistUrlTests" do
    let gistId = GistId "9d8feacacd8c4b553f870c4448483938"
    test "Ref" $ equalWithFormatter gShow (Right gistId) (parseGistUrl "9d8feacacd8c4b553f870c4448483938")
    test "Direct link" $ equalWithFormatter gShow (Right gistId) (parseGistUrl "https://gist.github.com/9d8feacacd8c4b553f870c4448483938")
    test "User link" $ equalWithFormatter gShow (Right gistId) (parseGistUrl "https://gist.github.com/krisajenkins/9d8feacacd8c4b553f870c4448483938")
    test "No ID" $ equalWithFormatter gShow (Left "Could not parse Gist Url") (parseGistUrl "https://gist.github.com/")
    test "Too long" $ equalWithFormatter gShow (Left  "Could not parse Gist Url") (parseGistUrl "aaaabbbbccccddddeeeeffff000011112")

equalWithFormatter :: forall a e. Eq a => (a -> String) -> a -> a -> Test e
equalWithFormatter f expected actual =
  if expected == actual then success

  else failure $ "expected " <> f expected <>
       ", got " <> f actual
