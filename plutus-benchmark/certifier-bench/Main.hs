{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Main where

import Control.Lens ((&), (.~))
import Control.Monad.Trans.Except
import Criterion.Main
import Data.ByteString qualified as B
import Data.ByteString.Short qualified as SBS
import FFI.SimplifierTrace
import FFI.Untyped (UTerm)
import MAlonzo.Code.VerifiedCompilation (runCertifierMain)
import Paths_plutus_benchmark
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
      <$> B.readFile (root </> "certifier-bench" </> "data" </> name)
  let Right term = runQuote . runExceptT $ UPLC.unDeBruijnTerm (UPLC._progTerm prog)
  pure . runQuote $ mkFfiSimplifierTrace . snd <$> simplify term

certify :: Trace UTerm -> ()
certify trace = case runCertifierMain trace of
  Just True -> ()
  _ -> error "Certification failed"

main :: IO ()
main = do
  queens <- loadFrom "n-queens.uplc"
  coop <- loadFrom "coop.uplc"
  vesting <- loadFrom "linear-vesting.uplc"
  loans <- loadFrom "cardano-loans.uplc"
  marlowe <- loadFrom "marlowe.uplc"
  defaultMain
    [ bench "N Queens" $ nf certify queens
    , bench "Cardano Open Oracle Protocol" $ nf certify coop
    , bench "Linear Vesting" $ nf certify vesting
    , bench "Cardano Loans" $ nf certify loans
    , bench "Marlowe" $ nf certify marlowe
    ]

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
          & soMaxCseIterations .~ 0
          & soPreserveLogging .~ False
      )
      DefaultFunSemanticsVariantE
