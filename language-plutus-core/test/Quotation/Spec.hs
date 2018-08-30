{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}

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
  asGolden (runQuote false) "test/Quotation/false.plc",
  asGolden (runQuote free) "test/Quotation/free.plc"
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
bool = do
    u <- unit
    [plcType|(all a (type) (fun (fun u a) (fun (fun u a) a))) |]

true :: Quote (Term TyName Name ())
true = do
    u <- unit
    o <- one
    [plcTerm|(abs a (type) (lam x (fun u a) (lam y (fun u a) [x o])))|]

false :: Quote (Term TyName Name ())
false = do
    u <- unit
    o <- one
    [plcTerm|(abs a (type) (lam x (fun u a) (lam y (fun u a) [y o])))|]

free :: Quote (Term TyName Name ())
free = do
  -- both occurences should be the same variable
  f <- TyVar () <$> freshTyName () "free"
  [plcTerm|[(lam x f x) (lam x f x)]|]
