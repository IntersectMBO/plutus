{-# LANGUAGE QuasiQuotes #-}

module Quotation.Spec (tests) where

import           Language.PlutusCore

import qualified Data.ByteString.Lazy as BSL
import           Data.Text.Encoding   (encodeUtf8)

import           Test.Tasty
import           Test.Tasty.Golden

tests :: TestTree
tests = testGroup "quasiquoter" [
  asGolden (runQuote unit) "test/Quotation/unit.plc",
  asGolden (runQuote one) "test/Quotation/one.plc",
  asGolden (runQuote bool) "test/Quotation/bool.plc",
  asGolden (runQuote true) "test/Quotation/true.plc",
  asGolden (runQuote false) "test/Quotation/false.plc"
 ]

asGolden :: PrettyCfg a => a -> TestName -> TestTree
asGolden a file = goldenVsString file (file ++ ".golden") (pure $ showTest a)

showTest :: PrettyCfg a => a -> BSL.ByteString
showTest = BSL.fromStrict . encodeUtf8 . debugText

unit :: Quote (Type TyName ())
unit = [plcType|(all a (type) (fun a a))|]

one :: Quote (Term TyName Name ())
one = [plcTerm|(abs a (type) (lam x a x))|]

bool :: Quote (Type TyName ())
bool = [plcType|(all a (type) (fun (fun unit a) (fun (fun unit a) a))) |]

true :: Quote (Term TyName Name ())
true = [plcTerm|(abs a (type) (lam x (fun unit a) (lam y (fun unit a) [x one])))|]

false :: Quote (Term TyName Name ())
false = [plcTerm|(abs a (type) (lam x (fun unit a) (lam y (fun unit a) [x one])))|]
