module Certifier.Common where

import Control.Lens ((&), (.~))
import Control.Monad.Trans.Except
import Data.ByteString qualified as B
import Data.ByteString.Short qualified as SBS
import FFI.SimplifierTrace
import FFI.Untyped (UTerm)
import PlutusBenchmark.Common (getDataDir)
import PlutusCore.Default.Builtins
import PlutusCore.Quote
import PlutusLedgerApi.Common
import System.FilePath
import UntypedPlutusCore as UPLC

loadFrom :: FilePath -> IO (Trace UTerm)
loadFrom name = do
  root <- getDataDir
  prog <-
    UPLC.programMapNames UPLC.fakeNameDeBruijn . uncheckedDeserialiseUPLC . SBS.toShort
      <$> B.readFile (root </> "certifier" </> "data" </> name)
  let term =
        either
          ( \e ->
              error $
                "Certifier.Common.loadFrom: program from "
                  <> name
                  <> " is ill-scoped: "
                  <> show e
          )
          id
          . runQuote
          . runExceptT
          $ UPLC.unDeBruijnTerm (UPLC._progTerm prog)
  pure . runQuote $ mkFfiSimplifierTrace . snd <$> simplify term

simplify
  :: Term Name DefaultUni DefaultFun ()
  -> Quote
       ( Term Name DefaultUni DefaultFun ()
       , SimplifierTrace Name DefaultUni DefaultFun ()
       )
simplify =
  runSimplifierT
    . termSimplifier
      ( defaultSimplifyOpts
          & soPreserveLogging .~ False
      )
      DefaultFunSemanticsVariantE

testScripts :: [FilePath]
testScripts =
  [ "n-queens.uplc"
  , "coop.uplc"
  , "linear-vesting.uplc"
  , "cardano-loans.uplc"
  , "marlowe-semantics.uplc"
  , "marlowe-semantics-data.uplc"
  , "marlowe-rolepayout.uplc"
  , "marlowe-rolepayout-data.uplc"
  , "guardrail-sorted.uplc"
  , "guardrail-unsorted.uplc"
  , "guardrail-sorted-data.uplc"
  , "guardrail-unsorted-data.uplc"
  ]
