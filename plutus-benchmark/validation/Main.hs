{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import qualified Language.PlutusCore                                        as PLC
import           Language.PlutusCore.CBOR
import           Language.PlutusCore.Constant                               (DynamicBuiltinNameMeanings (..))
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import qualified Language.PlutusCore.Pretty                                 as PP

import           Criterion.Main
import           Criterion.Types                                            (Config (..))
import qualified Language.PlutusCore.Universe                               as PLC
import qualified Language.UntypedPlutusCore                                 as UPLC
import qualified Language.UntypedPlutusCore.DeBruijn                        as UPLC
import qualified Language.UntypedPlutusCore.Evaluation.Machine.Cek          as UPLC
import           Paths_plutus_benchmark                                     (getDataFileName)

import           Control.Monad
import           Control.Monad.Trans.Except                                 (runExceptT)
import qualified Data.ByteString.Lazy                                       as BSL
import           Data.Functor                                               (($>), (<&>))
import qualified Data.Map                                                   as Map
import qualified Data.Text.IO                                               as T
import           System.FilePath
import           Text.Printf                                                (printf)

{-- | This set of benchmarks is based on validations occurring in the tests in
  plutus-use-cases.  Those tests are run on the blockchain simulator, and a
  modified version of Ledger.Scripts was used to extract validator scripts and
  their arguments.  These are stored in the `data` directory as Plutus Core
  source code, along with README files explaining which scripts were involved in
  each validation during the tests.  --}

type Term a    = UPLC.Term PLC.Name PLC.DefaultUni a
type Program a = UPLC.Program PLC.Name PLC.DefaultUni a
type PlcParserError = PLC.Error PLC.DefaultUni PLC.AlexPosn

loadPlcSource :: FilePath -> IO (Program ())
loadPlcSource file = do
  contents <- BSL.readFile file
  PLC.runQuoteT $ runExceptT (UPLC.parseScoped contents) >>= \case
     Left (err::PlcParserError) -> error $ "Parser error: " ++ PP.displayPlcDef err
     Right p                    -> return $ () <$ p

benchCek :: Term () -> Benchmarkable
benchCek program = nf (UPLC.unsafeEvaluateCek getStringBuiltinMeanings defaultCostModel) program


plcSuffix :: String
plcSuffix = "plc"

{- Construct an applied validator.  We assume that relevant validators, datum
   scripts, redeemers and contexts are stored in CBOR format under `<progName>`
   in the `data` directory.  These should have names like "Redeemer01.cbor",
   "Context03.cbor", and so on. This function returnes a Criterion environment
   to be fed to the relevant benchmark, to keep the IO overhead out of the
   benchmark itself. -}
getAppliedScript :: String -> Int -> Int -> Int -> Int -> IO (Term ())
getAppliedScript progName validatorNumber datumNumber redeemerNumber contextNumber = do
  let loadScript base scriptNumber = do
          let file = "bench-validation" </> "data" </> progName </> (base ++ printf "%02d" scriptNumber) <.> plcSuffix
          dataPath <- getDataFileName file
          loadPlcSource dataPath
  validator <- loadScript "Validator" validatorNumber
  datum     <- loadScript "Datum"     datumNumber
  redeemer  <- loadScript "Redeemer"  redeemerNumber
  context   <- loadScript "Context"   contextNumber
  let appliedValidator = validator `UPLC.applyProgram` datum `UPLC.applyProgram` redeemer `UPLC.applyProgram` context
  pure $ void . UPLC.toTerm $ appliedValidator

{- Create a benchmark with a name like "crowdfunding/5" by applying validator
   number v to datum number d, redeemer number r, and context number c in the
   directory data/<dirname>.  The 'id' argument is just to make the names of the
   indvidual benchmarks more readable and more easily typed. -}
mkBM :: String -> (Int, (Int, Int, Int, Int)) -> Benchmark
mkBM dirname (id, (v,d,r,c)) =
    env (getAppliedScript dirname v d r c) $ \script -> bench (show id) $ benchCek script

-- Make a `bgroup` collecting together a number of benchmarks for the same contract
mkBgroup :: String -> [(Int, (Int, Int, Int, Int))] -> Benchmark
mkBgroup dirname bms = bgroup dirname (map (mkBM dirname) bms)

{- See the README files in the data directories for the combinations of scripts.
   you can run specific benchmarks by typing things like
   `stack bench -- plutus-benchmark:validation --ba crowdfunding/2`. -}
{- The definition of `config` below will cause an HTML report to be generated.  If
   run via stack/cabal this will be written to the `plutus-benchmark` directory
   by default.  The -o option can be used to change this, but an absolute path
   will probably be required (eg, "-o=$PWD/report.html") . -}
main = do
  templateDir <- getDataFileName "templates"
  let templateFile = templateDir </> "with-iterations" <.> "tpl" -- Include number of iterations in HTML report
      config = defaultConfig {
                 template = templateFile,
                 reportFile = Just "report.html"
               }
  defaultMainWith config
       [ mkBgroup
         "crowdfunding"
         [ (1, (1,1,1,1))
         , (2, (1,2,1,2))
         , (3, (1,3,1,3))
         , (4, (1,3,2,4))
         , (5, (1,1,2,5))
         ]
       , mkBgroup
         "future"
         [ (1, (1,1,1,1))
         , (2, (2,2,1,2))
         , (3, (2,3,1,3))
         , (4, (3,4,2,4))
         , (5, (3,5,3,5))
         , (6, (3,4,4,6))
         , (7, (3,4,3,7))
         ]
       , mkBgroup
         "multisigSM"
         [ (1,  (1,1,1,1))
         , (2,  (1,2,2,2))
         , (3,  (1,3,3,3))
         , (4,  (1,4,4,4))
         , (5,  (1,5,5,5))
         , (6,  (1,1,1,6))
         , (7,  (1,2,2,7))
         , (8,  (1,3,3,8))
         , (9,  (1,4,4,9))
         , (10, (1,5,5,10))
         ]
       , mkBgroup
         "vesting"
         [ (1,  (1,1,1,1))
         , (2,  (2,1,1,2))
         , (3,  (3,1,1,1))
         ]
       , mkBgroup
         "marlowe/trustfund"
         [ (1,  (1,1,1,1))
         , (2,  (1,2,2,2))
         ]
       , mkBgroup
         "marlowe/zerocoupon"
         [ (1,  (1,1,1,1))
         , (2,  (1,2,2,2))
         ]
       ]
