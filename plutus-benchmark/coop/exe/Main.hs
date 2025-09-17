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
import PlutusCore.Flat (flat, unflat)
import System.Directory (doesFileExist)
import System.FilePath ((<.>), (</>))

import PlutusCore.Annotation (SrcSpans)
import PlutusLedgerApi.V2 (Datum (Datum), Redeemer (Redeemer))
import PlutusTx.Code (CompiledCodeIn (DeserializedCode, SerializedCode))
import PlutusTx.Test.Util.Apply (unsafeApplyCodeN)
import UntypedPlutusCore qualified as UPLC

import PlutusBenchmark.Common (getDataDir)
import PlutusBenchmark.Coop.Scripts qualified as Scripts
import PlutusBenchmark.Coop.TestContext
import PlutusBenchmark.Coop.Types

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
    scripts =
      [ unsafeApplyCodeN
          Scripts.fsV
          (liftCodeDef $ Datum $ toBuiltinData ())
          (liftCodeDefAsData ())
          (liftCodeDefAsData correctMustBurnOwnSingletonValueContext)

      , unsafeApplyCodeN
          Scripts.certMp
          (liftCodeDef certMpParams)
          (liftCodeDefAsData $ Redeemer $ toBuiltinData CertMpMint)
          (liftCodeDefAsData correctCertMpMintingContext)
      , unsafeApplyCodeN
          Scripts.certMp
          (liftCodeDef certMpParams)
          (liftCodeDefAsData $ Redeemer $ toBuiltinData CertMpBurn)
          (liftCodeDefAsData correctCertMpBurningContext)

      , unsafeApplyCodeN
          Scripts.fsMp
          (liftCodeDef fsMpParams)
          (liftCodeDefAsData $ Redeemer $ toBuiltinData FsMpMint)
          (liftCodeDefAsData correctFsMpMintingContext)
      , unsafeApplyCodeN
          Scripts.fsMp
          (liftCodeDef fsMpParams)
          (liftCodeDefAsData $ Redeemer $ toBuiltinData FsMpBurn)
          (liftCodeDefAsData correctFsMpBurningContext)

      , unsafeApplyCodeN
          Scripts.authMp
          (liftCodeDef authMpParams)
          (liftCodeDefAsData $ Redeemer $ toBuiltinData AuthMpMint)
          (liftCodeDefAsData correctAuthMpMintingContext)
      , unsafeApplyCodeN
          Scripts.authMp
          (liftCodeDef authMpParams)
          (liftCodeDefAsData $ Redeemer $ toBuiltinData AuthMpBurn)
          (liftCodeDefAsData correctAuthMpBurningContext)
      ]

  traverse_ (uncurry createIfNotExists) (zip ((\i -> "coop-" <> show @Integer i) <$> [1..]) scripts)
  pure ()
