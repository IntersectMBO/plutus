{-# LANGUAGE NumericUnderscores #-}
module Cardano.Constitution.Validator.Empty.GoldenTests
    ( tests
    ) where

import Cardano.Constitution.Validator
import Cardano.Constitution.Config
import PlutusCore.Pretty (prettyPlcReadable)
import PlutusTx.Code as Tx

import Test.Tasty
import Test.Tasty.Golden
import Test.Tasty.HUnit
import Data.Map.Strict qualified as M
import PlutusLedgerApi.V3 as V3
import Data.ByteString.Short qualified as SBS
import Data.String
import System.FilePath
import Data.Maybe

mkPath :: String -> [String] -> FilePath
mkPath vName exts = foldl1 (</>) ["test","Cardano","Constitution","Validator","Empty","GoldenTests", foldl (<.>) vName (exts++["golden"])]

-- smallest valid config (empty config). Used to test size of scripts and print code
emptyCfg :: ConstitutionConfig
emptyCfg = ConstitutionConfig []

test_cbor, test_cbor_unit, test_cbor_golden, test_readable_pir, test_readable_uplc, tests :: TestTree

test_cbor = testGroup "Cbor" [test_cbor_unit, test_cbor_golden]

test_cbor_unit = testGroup "Unit" $ M.elems $
    (\vName vCode -> testCase vName $
         let -- current maxTxSize is 16384 Bytes set on 07/29/2020 23:44:51
             -- , but we set this limit a bit lower (to accomodate other tx costs?)
             maxTxSize = 10_000
             emptySize = SBS.length $ V3.serialiseCompiledCode $ vCode emptyCfg
         in assertBool "EmptyConstitution does not fit transaction-size limits." (emptySize < maxTxSize)
    ) `M.mapWithKey` validatorCodes

test_cbor_golden = testGroup "Golden" $ M.elems $
    (\vName vCode ->
         -- The unit of measurement is in bytes
         goldenVsString vName (mkPath vName ["cbor","size"]) $
            pure $ fromString $ show $ SBS.length $ V3.serialiseCompiledCode $ vCode emptyCfg
    ) `M.mapWithKey` validatorCodes

test_readable_pir = testGroup "ReadablePir" $ M.elems $
    (\vName vCode ->
         goldenVsString vName (mkPath vName ["pir"]) $
            pure $ fromString $ show $ prettyPlcReadable $ fromJust $ getPirNoAnn $ vCode emptyCfg
    )`M.mapWithKey` validatorCodes

test_readable_uplc = testGroup "ReadableUplc" $ M.elems $
    (\vName vCode ->
         goldenVsString vName (mkPath vName ["uplc"]) $
            pure $ fromString $ show $ prettyPlcReadable $ getPlcNoAnn $ vCode emptyCfg
    )`M.mapWithKey` validatorCodes

tests = testGroup "Golden"
        [ test_cbor
        , test_readable_pir
        , test_readable_uplc
        ]
