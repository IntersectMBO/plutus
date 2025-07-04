{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

{-
This module itself won't run any benchmark on it's own. It will only generate `.flat` file, if
missing, in `validation/data` directory for `validation` benchmark runner to run COOP scripts.
-}

module Main where

import PlutusTx

import Data.ByteString.Lazy qualified as BSL
import Data.Foldable (traverse_)
import Flat (flat, unflat)
import System.Directory (doesFileExist)
import System.FilePath ((<.>), (</>))
import Test.QuickCheck.Gen (Gen (unGen))
import Test.QuickCheck.Random (mkQCGen)

import PlutusCore.Annotation (SrcSpans)
import PlutusLedgerApi.V1.Address (scriptHashAddress)
import PlutusLedgerApi.V1.Value (AssetClass, assetClass)
import PlutusLedgerApi.V2 (Address, CurrencySymbol (CurrencySymbol), Datum (Datum),
                           Redeemer (Redeemer), ScriptHash (ScriptHash), TokenName (TokenName))
import PlutusTx.Code (CompiledCodeIn (DeserializedCode, SerializedCode))
import PlutusTx.Test.Util.Apply (unsafeApplyCodeN)
import UntypedPlutusCore qualified as UPLC

import PlutusBenchmark.Common (getDataDir)
import PlutusBenchmark.Coop.Gen qualified as CG
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
    eraseName (UPLC.Program ann ver t) =
      () <$ UPLC.Program ann ver (UPLC.termMapNames UPLC.unNameDeBruijn t)
  termAsBS <-
    case term of
      SerializedCode bs _ _     ->
        let
          parsed =
            UPLC.unUnrestrictedProgram
              <$> unflat
                @( UPLC.UnrestrictedProgram
                     UPLC.NamedDeBruijn
                     UPLC.DefaultUni
                     UPLC.DefaultFun
                     SrcSpans
                 )
                bs
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
    size = 1
    runGen :: Gen a -> a
    runGen g = unGen g (mkQCGen seed) size
    scripts =
      [ unsafeApplyCodeN
          Scripts.fsV
          (liftCodeDef $ Datum $ toBuiltinData ())
          (liftCodeDefAsData ())
          (liftCodeDefAsData $ runGen CG.genCorrectMustBurnOwnSingletonValueCtx)

      , unsafeApplyCodeN
          Scripts.certMp
          (liftCodeDef certMpParams)
          (liftCodeDefAsData $ Redeemer $ toBuiltinData CertMpMint)
          (liftCodeDefAsData $ runGen $ CG.genCorrectCertMpMintingCtx certMpParams certCs)
      , unsafeApplyCodeN
          Scripts.certMp
          (liftCodeDef certMpParams)
          (liftCodeDefAsData $ Redeemer $ toBuiltinData CertMpBurn)
          (liftCodeDefAsData $
             runGen $ CG.genCertRdmrAc >>= CG.genCorrectCertMpBurningCtx certMpParams certCs)

      , unsafeApplyCodeN
          Scripts.fsMp
          (liftCodeDef fsMpParams)
          (liftCodeDefAsData $ Redeemer $ toBuiltinData FsMpMint)
          (liftCodeDefAsData $ runGen $ CG.genCorrectFsMpMintingCtx fsMpParams fsCs)
      , unsafeApplyCodeN
          Scripts.fsMp
          (liftCodeDef fsMpParams)
          (liftCodeDefAsData $ Redeemer $ toBuiltinData FsMpBurn)
          (liftCodeDefAsData $ runGen $ CG.genCorrectFsMpBurningCtx fsMpParams fsCs)

      , unsafeApplyCodeN
          Scripts.authMp
          (liftCodeDef authMpParams)
          (liftCodeDefAsData $ Redeemer $ toBuiltinData AuthMpMint)
          (liftCodeDefAsData $ runGen $ CG.genCorrectAuthMpMintingCtx authMpParams authCs)
      , unsafeApplyCodeN
          Scripts.authMp
          (liftCodeDef authMpParams)
          (liftCodeDefAsData $ Redeemer $ toBuiltinData AuthMpBurn)
          (liftCodeDefAsData $ runGen $ CG.genCorrectAuthMpBurningCtx authCs)
      ]

  traverse_ (uncurry createIfNotExists) (zip ((\i -> "coop-" <> show @Integer i) <$> [1..]) scripts)
  pure ()
