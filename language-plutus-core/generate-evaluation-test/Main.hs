{-# LANGUAGE OverloadedStrings #-}
module Main where

import           PlutusPrelude hiding (hoist)
import           Language.PlutusCore
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Constant
import           Language.PlutusCore.CkMachine
import           Language.PlutusCore.TestSupport

import           Data.Foldable
import           Control.Monad
import           Control.Monad.Morph
import qualified Data.Text.IO as Text
import qualified Hedgehog.Gen   as Gen

-- | Generate a test sample: a term of arbitrary type and what it computes to.
-- Uses 'genTermLoose' under the hood.
generateTerm :: IO (TermOf (Value TyName Name ()))
generateTerm
    = Gen.sample
    . Gen.just
    . hoist (pure . runQuote)
    $ withAnyTermLoose
    $ \(TermOf term tbv) -> pure $ do
          let expected = unsafeDupMakeConstant tbv
          actual <- ckEvalResultToMaybe $ evaluateCk term
          when (actual /= expected) $ error $ concat
              [ "An internal error in 'generateTerm' occured while computing ", prettyString term, "\n"
              , "Expected result: ", prettyString expected , "\n"
              , "Actual result: ", prettyString actual, "\n"
              ]
          Just $ TermOf term actual

main :: IO ()
main = do
    TermOf term value <- generateTerm
    traverse_ Text.putStrLn
        [ prettyText $ Program () (Version () 0 1 0) term
        , ""
        , prettyText value
        ]
