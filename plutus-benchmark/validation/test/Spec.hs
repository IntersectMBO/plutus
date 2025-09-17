{-# LANGUAGE TypeApplications #-}

module Main where

import Test.Tasty
import Test.Tasty.Extras (TestNested, runTestNested, testNestedGhc)

import PlutusBenchmark.NaturalSort
import PlutusBenchmark.Validation.Common

import PlutusCore.Annotation qualified as PLC
import PlutusTx.Code qualified as Tx
import PlutusTx.Test qualified as Tx
import UntypedPlutusCore qualified as UPLC

import Data.ByteString qualified as BS
import PlutusCore.Flat
import System.Directory (listDirectory)
import System.FilePath

runTestGhc :: [TestNested] -> TestTree
runTestGhc = runTestNested ["validation", "test"] . pure . testNestedGhc

mkCase :: FilePath -> FilePath -> IO TestNested
mkCase path name = do
  bs <- BS.readFile (path </> name)
  let
    parsed ::
      Either
        DecodeException
        (UPLC.Program UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun PLC.SrcSpans)
    parsed =
      (fmap mempty . UPLC.programMapNames UPLC.fakeNameDeBruijn . UPLC.unUnrestrictedProgram)
        <$> unflat @(UPLC.UnrestrictedProgram UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()) bs
  case parsed of
    Left err -> error $ show err
    Right parsed' ->
      pure $
        Tx.goldenEvalCekCatchBudget
          name
          (Tx.DeserializedCode parsed' Nothing mempty)

allTests :: IO TestTree
allTests = do
  scriptDirectory <- getScriptDirectory
  files <-
    (naturalSort . filter (isExtensionOf ".flat"))
      <$> listDirectory scriptDirectory

  runTestGhc <$> traverse (mkCase scriptDirectory) files

main :: IO ()
main = allTests >>= defaultMain
