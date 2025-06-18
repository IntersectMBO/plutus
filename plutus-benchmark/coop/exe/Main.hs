{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

{-
This module itself won't run any benchmark on it's own. It will only generate `.flat` file, if missing,
in `validation/data` directory for `validation` benchmark runner to run COOP scripts.
-}

module Main where

import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSL
import Flat (flat, unflat)
import System.Directory
import System.FilePath
import Test.QuickCheck.Gen
import Test.QuickCheck.Random

import PlutusCore.Annotation
import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V1.Value
import PlutusLedgerApi.V2
import PlutusTx
import PlutusTx.Code
import PlutusTx.Prelude qualified as PTx
import PlutusTx.Test.Util.Apply
import PlutusTx.TH
import UntypedPlutusCore qualified as UPLC

import PlutusBenchmark.Common
import PlutusBenchmark.Coop.Gen
import PlutusBenchmark.Coop.Scripts qualified as Scripts
import PlutusBenchmark.Coop.Types

-- Some Constants Used for Script Context --
coopAc :: AssetClass
coopAc = assetClass (CurrencySymbol "$COOP CurrencySymbol") (TokenName "$COOP TokenName")

aaAc :: AssetClass
aaAc = assetClass (CurrencySymbol "$AA CurrencySymbol") (TokenName "$AA TokenName")

certCs :: CurrencySymbol
certCs = CurrencySymbol "cert-policy- hash"

authCs :: CurrencySymbol
authCs = CurrencySymbol "auth-policy- hash"

fsCs :: CurrencySymbol
fsCs = CurrencySymbol "fs-policy- hash"

certVAddr :: Address
certVAddr = scriptHashAddress . ScriptHash $ "@CertV hash"

fsVAddr :: Address
fsVAddr = scriptHashAddress . ScriptHash $ "@FsV hash"

aaQ :: Integer
aaQ = 42

certMpParams :: CertMpParams
certMpParams = CertMpParams aaAc aaQ certVAddr

fsMpParams :: FsMpParams
fsMpParams = FsMpParams coopAc fsVAddr (AuthParams authCs certCs)

authMpParams :: AuthMpParams
authMpParams = AuthMpParams aaAc aaQ

getScriptDirectory :: IO FilePath
getScriptDirectory = do
  root <- getDataDir
  return $ root </> "validation" </> "data"

createIfNotExists :: String -> CompiledCode a -> IO ()
createIfNotExists name term = do
  p <- getScriptDirectory
  let
    fullName = p </> name <.> "flat"
    eraseName (UPLC.Program ann ver term) =
      () <$ UPLC.Program ann ver (UPLC.termMapNames UPLC.unNameDeBruijn term)
  termAsBS <-
    case term of
      SerializedCode bs _ _     ->
        let
          parsed =
            UPLC.unUnrestrictedProgram
            <$> (unflat @(UPLC.UnrestrictedProgram UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun SrcSpans) $ bs)
        in case parsed of
          Left err -> error $ "failed to parse UPLC flat from compiled code" <> show err
          Right parsed' ->
            pure $ BSL.fromStrict $ flat $ UPLC.UnrestrictedProgram $ eraseName parsed'
      DeserializedCode uplc _ _ ->
        pure $ BSL.fromStrict $ flat $ UPLC.UnrestrictedProgram $ eraseName uplc

  exists <- doesFileExist fullName

  if exists
    then putStrLn $ name <> " is already in place. No changes were made."
    else do
      BSL.writeFile fullName termAsBS
      putStrLn $ name <> " is been written."

liftCodeDefAsData :: ToData a => a -> CompiledCode BuiltinData
liftCodeDefAsData = liftCodeDef . toBuiltinData

main :: IO ()
main = do
  let
    seed = 1
    runGen :: Gen a -> a
    runGen g = unGen g (mkQCGen seed) 1
    scripts =
      [ compiledCodeToHaskUnsafe
          Scripts.fsV
          (liftCodeDef $ Datum $ toBuiltinData ())
          (liftCodeDefAsData ())
          (liftCodeDefAsData $ runGen genCorrectMustBurnOwnSingletonValueCtx)

      , compiledCodeToHaskUnsafe
          Scripts.certMp
          (liftCodeDef certMpParams)
          (liftCodeDefAsData (Redeemer $ toBuiltinData CertMpMint))
          (liftCodeDefAsData $ runGen (genCorrectCertMpMintingCtx certMpParams certCs))
      , compiledCodeToHaskUnsafe
          Scripts.certMp
          (liftCodeDef certMpParams)
          (liftCodeDefAsData (Redeemer $ toBuiltinData CertMpBurn))
          (liftCodeDefAsData $
             runGen (genCertRdmrAc >>= genCorrectCertMpBurningCtx certMpParams certCs))

      , compiledCodeToHaskUnsafe
          Scripts.fsMp
          (liftCodeDef fsMpParams)
          (liftCodeDefAsData (Redeemer $ toBuiltinData FsMpMint))
          (liftCodeDefAsData $ runGen (genCorrectFsMpMintingCtx fsMpParams fsCs))
      , compiledCodeToHaskUnsafe
          Scripts.fsMp
          (liftCodeDef fsMpParams)
          (liftCodeDefAsData (Redeemer $ toBuiltinData FsMpBurn))
          (liftCodeDefAsData $
             runGen (genCorrectFsMpBurningCtx fsMpParams fsCs))

      , compiledCodeToHaskUnsafe
          Scripts.authMp
          (liftCodeDef authMpParams)
          (liftCodeDefAsData (Redeemer $ toBuiltinData AuthMpMint))
          (liftCodeDefAsData $ runGen (genCorrectAuthMpMintingCtx authMpParams authCs))
      , compiledCodeToHaskUnsafe
          Scripts.authMp
          (liftCodeDef authMpParams)
          (liftCodeDefAsData (Redeemer $ toBuiltinData AuthMpBurn))
          (liftCodeDefAsData $
             runGen (genCorrectAuthMpBurningCtx authCs))
      ]

  traverse (uncurry createIfNotExists) (zip ((\i -> "coop-" <> show i) <$> [1..]) scripts)
  pure ()
