{-# LANGUAGE OverloadedStrings #-}
module Evaluation.CkMachine where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.CkMachine
import           Evaluation.Generator

import qualified Data.ByteString.Lazy as BSL
import           Control.Monad.Reader
import           Control.Monad.Morph
import           Hedgehog hiding (Size, Var, annotate)
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

parseRunCk :: BSL.ByteString -> Either ParseError CkEvalResult
parseRunCk = fmap (runCk . void) . parseScoped

blah = parseRunCk $ "(program 0.1.0 [(lam x [(con integer) (con 32)] x) (con 32 ! 123456)])"

test_constant :: TestTree
test_constant = testProperty "" . property $ do
    size <- forAll genSizeDef
    term <- forAll $ Constant () <$> genConstantSized size
    evaluateCk term === CkEvalSuccess term

main = defaultMain test_constant
