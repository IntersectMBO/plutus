{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

{-
This module itself won't run any benchmark on it's own. It will only generate `.flat` file, if missing,
in `validation/data` directory for `validation` benchmark runner to run COOP scripts.
-}

module Main where

import Language.Haskell.TH.Syntax qualified as TH

import Data.ByteString qualified as BS
import Flat (flat)
import System.Directory
import System.FilePath
import Test.QuickCheck.Gen
import Test.QuickCheck.Random

import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V1.Value
import PlutusLedgerApi.V2
import PlutusTx
import PlutusTx.Code
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
    termAsBS =
      case term of
        SerializedCode bs _ _     -> bs
        DeserializedCode uplc _ _ -> flat $ UPLC.UnrestrictedProgram uplc

  exists <- doesFileExist fullName

  if exists
    then putStrLn $ name <> " is already in place. No changes were made."
    else do
      BS.writeFile fullName termAsBS
      putStrLn $ name <> " is been written."

main :: IO ()
main = do
  let
    fsVCompiled = $$(compile [|| Scripts.fsV ||])
    certVCompiled = $$(compile [|| Scripts.certV ||])
    fsMpCompiled = $$(compile [|| Scripts.fsMp fsMpParams ||])
    certMpCompiled = $$(compile [|| Scripts.certMp certMpParams ||])
    authMpCompiled = $$(compile [|| Scripts.authMp ||])
    scripts =
      [ compiledCodeToHaskUnsafe
          certMpCompiled
          (liftCodeDef (Redeemer $ toBuiltinData CertMpMint))
          (liftCodeDef $ unGen (genCorruptCertMpMintingCtx certMpParams certCs) (mkQCGen 42) 1)
      , compiledCodeToHaskUnsafe
          certMpCompiled
          (liftCodeDef (Redeemer $ toBuiltinData CertMpMint))
          (liftCodeDef $ unGen (genCorrectCertMpMintingCtx certMpParams certCs) (mkQCGen 42) 1)
      , compiledCodeToHaskUnsafe
          certMpCompiled
          (liftCodeDef (Redeemer $ toBuiltinData CertMpBurn))
          (liftCodeDef $
             unGen (genCertRdmrAc >>= genCorruptCertMpBurningCtx certMpParams certCs) (mkQCGen 42) 1)
      , compiledCodeToHaskUnsafe
          certMpCompiled
          (liftCodeDef (Redeemer $ toBuiltinData CertMpBurn))
          (liftCodeDef $
             unGen (genCertRdmrAc >>= genCorrectCertMpBurningCtx certMpParams certCs) (mkQCGen 42) 1)

      , compiledCodeToHaskUnsafe
          fsMpCompiled
          (liftCodeDef (Redeemer $ toBuiltinData FsMpMint))
          (liftCodeDef $ unGen (genCorruptFsMpMintingCtx fsMpParams certCs) (mkQCGen 42) 1)
      , compiledCodeToHaskUnsafe
          fsMpCompiled
          (liftCodeDef (Redeemer $ toBuiltinData FsMpMint))
          (liftCodeDef $ unGen (genCorrectFsMpMintingCtx fsMpParams certCs) (mkQCGen 42) 1)
      , compiledCodeToHaskUnsafe
          fsMpCompiled
          (liftCodeDef (Redeemer $ toBuiltinData FsMpBurn))
          (liftCodeDef $
             unGen (genCorruptFsMpBurningCtx fsMpParams certCs) (mkQCGen 42) 1)
      , compiledCodeToHaskUnsafe
          fsMpCompiled
          (liftCodeDef (Redeemer $ toBuiltinData FsMpBurn))
          (liftCodeDef $
             unGen (genCorrectFsMpBurningCtx fsMpParams certCs) (mkQCGen 42) 1)
      ]

  traverse (uncurry createIfNotExists) (zip ((\i -> "coop-" <> show i <> ".flat") <$> [1..]) scripts)
  pure ()

-- unGen (genCorrectCertMpMintingCtx certMpParams certCs) (mkQCGen 42) 1

{-
passing-cert-policy-minting.flat
failing-cert-policy-minting.flat
passing-cert-policy-burning.flat
failing-cert-policy-burning.flat

passing-auth-policy-minting.flat
failing-auth-policy-minting.flat
passing-auth-policy-burning.flat
failing-auth-policy-burning.flat

passing-fs-policy-minting.flat
failing-fs-policy-minting.flat
passing-fs-policy-burning.flat
failing-fs-policy-burning.flat

passing-cert-validator-Spending.flat
failing-cert-validator-Spending.flat

passing-MustBurnOwnSingletonValue-validator.flat
failing-MustBurnOwnSingletonValue-validator.flat

passing-fs-validator-spending.flat
failing-fs-validator-spending.flat
-}
