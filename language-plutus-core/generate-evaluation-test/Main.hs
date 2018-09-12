{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.CkMachine
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Generators

import           Control.Monad
import           Control.Monad.Morph
import           Data.Foldable
import           Data.Text                                (Text)
import qualified Data.Text                                as Text
import qualified Data.Text.IO                             as Text
import qualified Hedgehog.Gen                             as Gen

-- | Generate a test sample: a term of arbitrary type and what it computes to.
-- Uses 'genTermLoose' under the hood.
generateTerm :: IO (TermOf (Value TyName Name ()))
generateTerm
    = Gen.sample
    . Gen.just
    . hoist (pure . runQuote)
    $ withAnyTermLoose
    $ \(TermOf term tbv) -> pure $ do
          let expected = runQuote $ unsafeMakeBuiltin tbv
          actual <- evaluationResultToMaybe $ evaluateCk term
          when (actual /= expected) . error $ fold
              [ "An internal error in 'generateTerm' occured while computing "
              , prettyCfgString term, "\n"
              , "Expected result: ", prettyCfgString expected , "\n"
              , "Actual result: ", prettyCfgString actual, "\n"
              ]
          Just $ TermOf term actual

oneline :: Text -> Text
oneline = Text.unwords . Text.words

main :: IO ()
main = do
    TermOf term value <- generateTerm
    traverse_ Text.putStrLn
        [ oneline . prettyCfgText $ Program () (Version () 0 1 0) term
        , ""
        , oneline $ prettyCfgText value
        ]
