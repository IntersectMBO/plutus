-- editorconfig-checker-disable-file
module Main where

import Cardano.Constitution.Config.Tests qualified as ConfigTests
import Cardano.Constitution.Validator.Data.GoldenTests qualified as Data.GoldenTests
import Cardano.Constitution.Validator.Data.PropTests qualified as Data.PropTests
import Cardano.Constitution.Validator.Data.UnitTests qualified as Data.UnitTests
import Cardano.Constitution.Validator.GoldenTests qualified as GoldenTests
import Cardano.Constitution.Validator.PropTests qualified as PropTests
import Cardano.Constitution.Validator.UnitTests qualified as UnitTests
import Control.Exception
import Data.Aeson
import Data.ByteString.Char8 qualified as BS
import Data.IORef
import Helpers.Guardrail (allParams)
import Helpers.MultiParam
import Helpers.Spec.FareySpec qualified as FareySpec
import Helpers.Spec.IntervalSpec qualified as IntervalSpec
import Helpers.TestBuilders
import System.Directory
import System.Exit
import System.FilePath
import System.IO ()
import Test.Tasty (defaultMainWithIngredients, localOption)
import Test.Tasty.Ingredients.Basic
import Test.Tasty.JsonReporter
import Test.Tasty.QuickCheck qualified as TQC

expectTrue :: (a, b) -> a
expectTrue = fst

expectFalse :: (Bool, b) -> Bool
expectFalse = not . fst

main :: IO ()
main = do
  -- initialize the state for tests results
  ref <- newIORef (TestState mempty mempty)

  -- tests to be run
  let mainTest =
        testGroup'
          "Testing Campaign"
          [ UnitTests.unitTests
          , PropTests.tests
          , ConfigTests.tests
          , GoldenTests.tests
          , UnitTests.singleParamTests
          , Data.UnitTests.unitTests
          , Data.PropTests.tests
          , Data.GoldenTests.tests
          , Data.UnitTests.singleParamTests
          , testGroup'
              "Multiple Parameter Changes"
              [ testProperty' "Proposal with all parameters at their current (or default value if new)" $
                  multiParamProp 1 (allValid allParams) expectTrue
              , testProperty' "Proposals with one parameter missing, and all the other ones within their ranges" $
                  multiParamProp 2 (allValidAndOneMissing allParams) expectTrue
              , testProperty' "Proposals with one parameter lower than its lower bound, and all the other ones within their ranges" $
                  multiParamProp 3 (allValidAndOneLessThanLower allParams) expectFalse
              , testProperty' "Proposals with one parameter greater than its upper bound, and all the other ones within their ranges" $
                  multiParamProp 4 (allValidAndOneGreaterThanUpper allParams) expectFalse
              , testProperty' "Proposals with one parameter unknown and all the other ones within their ranges" $
                  multiParamProp 5 (allValidAndOneUnknown allParams) expectFalse
              , testProperty' "Proposals with all parameters but one, all within their ranges, plus one unknown" $ -- To see if they don't do a trick on proposal length
                  multiParamProp 6 (allValidButOnePlusOneUnknown allParams) expectFalse
              , testProperty' "Proposals with all parameters within their ranges" $
                  multiParamProp 7 (allValid allParams) expectTrue
              , testProperty' "Proposals with all parameters outside their ranges " $
                  multiParamProp 8 (allInvalid allParams) expectFalse
              , testProperty' "Proposals with a selection of parameters within their ranges" $
                  multiParamProp 9 (someValidParams allParams) expectTrue
              , testProperty' "Proposals with a selection of parameters, some within their ranges, some outside" $
                  multiParamProp 10 (someInvalidAndSomeValidParams allParams) expectFalse
              , testProperty' "Proposals with a selection of parameters within their ranges + costModels" $
                  multiParamProp' 11 (someValidParams allParams) ((: []) <$> costModelsParamGen) expectTrue
              , testProperty' "Proposals with a selection of parameters, some within their ranges, some outside + costModels" $
                  multiParamProp' 12 (someInvalidAndSomeValidParams allParams) ((: []) <$> costModelsParamGen) expectFalse
              ]
          , testGroup'
              "Internal Tests"
              [ const IntervalSpec.internalTests
              , const FareySpec.internalTests
              ]
          ]

  let testTree =
        localOption (TQC.QuickCheckTests 30) $
          mainTest ref

  -- run the tests
  defaultMainWithIngredients [listingTests, consoleAndJsonReporter] testTree
    `catch` ( \(e :: ExitCode) -> do
                -- write the results to a file
                (TestState oneParamS multiParamS) <- readIORef ref
                let directory = "certification" </> "data"
                createDirectoryIfMissing True directory
                BS.writeFile (directory </> "single-param.json") $ BS.toStrict $ encode oneParamS
                BS.writeFile (directory </> "multi-param.json") $ BS.toStrict $ encode multiParamS
                putStrLn $ "JSON files written to " <> directory
                throwIO e
            )
