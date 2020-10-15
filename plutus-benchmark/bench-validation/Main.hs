{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Criterion.Main
import           Criterion.Types                                            (Config (..))

import           Codec.Serialise
import           Control.Monad
import           Control.Monad.Trans.Except                                 (runExceptT)
import qualified Data.ByteString.Lazy                                       as BSL
import           Data.Functor                                               ((<&>))
import qualified Data.Map                                                   as Map
import           System.FilePath

import qualified Language.PlutusCore                                        as PLC
import           Language.PlutusCore.CBOR
import           Language.PlutusCore.Constant                               (DynamicBuiltinNameMeanings (..))
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import qualified Language.PlutusCore.Universe                               as PLC
import qualified Language.UntypedPlutusCore                                 as UPLC
import qualified Language.UntypedPlutusCore.DeBruijn                        as UPLC
import qualified Language.UntypedPlutusCore.Evaluation.Machine.Cek          as UPLC

emptyBuiltins :: DynamicBuiltinNameMeanings (UPLC.CekValue PLC.DefaultUni)
emptyBuiltins =  DynamicBuiltinNameMeanings Map.empty

config :: Config
config = defaultConfig
  { reportFile = Just "report.html"
  , jsonFile = Just "report.json"
  }

fromDeBruijn ::  UPLC.Program UPLC.DeBruijn PLC.DefaultUni a ->  IO (UPLC.Program PLC.Name PLC.DefaultUni a)
fromDeBruijn prog = do
    let namedProgram = UPLC.programMapNames (\(UPLC.DeBruijn ix) -> UPLC.NamedDeBruijn "v" ix) prog
    case PLC.runQuote $ runExceptT $ UPLC.unDeBruijnProgram namedProgram of
      Left e  -> error $ show e
      Right p -> return p

loadPlc :: Serialise a => FilePath -> IO (UPLC.Program PLC.Name PLC.DefaultUni a)
loadPlc file = do
  BSL.readFile file <&> deserialiseOrFail >>= mapM fromDeBruijn >>= \case
               Left (DeserialiseFailure offset msg) ->
                   error ("Deserialisation failure at offset " ++ Prelude.show offset ++ ": " ++ msg)
               Right r -> return r

benchCek :: UPLC.Term PLC.Name PLC.DefaultUni () -> Benchmarkable
benchCek program = nf (UPLC.unsafeEvaluateCek getStringBuiltinMeanings defaultCostModel) program

cborSuffix :: String
cborSuffix = ".cbor"

dataDir :: String
dataDir = "/home/kwxm/plutus/plutus/plutus-benchmark/bench-validation" </> "data"


{- Construct an applied validator.  We assume that relevant validators, datum
   scripts, redeemers and contexts are stored in CBOR format under `<progName>`
   in the `data` directory.  These should have names like "Redeemer1.cbor", "Context3.cbor",
   and so on. This function returnes a Criterion environment to be fed to the relevant
   benchmark, to keep the IO overhead out of the benchmark itself. -}
getAppliedScript progName validatorNumber datumNumber redeemerNumber contextNumber = do
  let dataPath = dataDir </> progName
      loadScript base suffix = do
          let file = dataPath </> (base ++ show suffix ++ cborSuffix)
          loadPlc file
  validator <- loadScript "Validator" validatorNumber
  datum     <- loadScript "Datum" datumNumber
  redeemer  <- loadScript "Redeemer" redeemerNumber
  context   <- loadScript "Context" contextNumber
  let appliedValidator = validator `UPLC.applyProgram` datum `UPLC.applyProgram` redeemer `UPLC.applyProgram` context
  pure $ void . UPLC.toTerm $ appliedValidator



main :: IO ()
main = defaultMainWith config
       [
         bgroup "crowdfunding" [
                      env (getAppliedScript "Crowdfunding" 1 1 1 1) $ \ ~ script -> bench "Crowdfunding1" $ benchCek script
                    , env (getAppliedScript "Crowdfunding" 1 2 1 2) $ \ ~ script -> bench "Crowdfunding2" $ benchCek script
                    , env (getAppliedScript "Crowdfunding" 1 3 1 3) $ \ ~ script -> bench "Crowdfunding3" $ benchCek script
                    , env (getAppliedScript "Crowdfunding" 1 3 1 4) $ \ ~ script -> bench "Crowdfunding4" $ benchCek script
                    , env (getAppliedScript "Crowdfunding" 1 1 2 5) $ \ ~ script -> bench "Crowdfunding5" $ benchCek script
                    , env (getAppliedScript "Crowdfunding" 1 3 2 5) $ \ ~ script -> bench "CrowdfundingX" $ benchCek script
                    ]
       , bgroup "Future" [
                      env (getAppliedScript "Future" 1 1 1 1) $ \ ~ script -> bench "Future1" $ benchCek script
                    , env (getAppliedScript "Future" 2 2 1 2) $ \ ~ script -> bench "Future2" $ benchCek script
                    , env (getAppliedScript "Future" 2 3 1 4) $ \ ~ script -> bench "Future3" $ benchCek script
                    , env (getAppliedScript "Future" 3 4 2 4) $ \ ~ script -> bench "Future4" $ benchCek script
                    , env (getAppliedScript "Future" 3 5 3 5) $ \ ~ script -> bench "Future5" $ benchCek script
                    , env (getAppliedScript "Future" 3 4 4 6) $ \ ~ script -> bench "Future6" $ benchCek script
                    , env (getAppliedScript "Future" 3 4 3 7) $ \ ~ script -> bench "Future7" $ benchCek script
                    , env (getAppliedScript "Future" 3 5 4 7) $ \ ~ script -> bench "FutureX" $ benchCek script
                    ]
       ]
