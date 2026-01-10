-- editorconfig-checker-disable-file
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

-- | Various analyses of events in mainnet script dumps.
module Main (main) where

import LoadScriptEvents (eventsOf, loadEvents)

import Data.Vector.Strict qualified as Vector
import PlutusCore.Data as Data (Data (..))
import PlutusCore.Default (DefaultUni (DefaultUniData), Some (..), ValueOf (..))
import PlutusCore.Evaluation.Machine.CostStream (sumCostStream)
import PlutusCore.Evaluation.Machine.ExMemoryUsage (ExMemoryUsage, flattenCostRose, memoryUsage)
import PlutusCore.Pretty (display)
import PlutusLedgerApi.Common
import PlutusLedgerApi.Test.EvaluationEvent
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3 qualified as V3
import PlutusTx.AssocMap qualified as M
import UntypedPlutusCore as UPLC

import Control.Exception (throwIO)
import Control.Lens hiding (List)
import Control.Monad.Primitive (PrimState)
import Control.Monad.Writer.Strict
import Data.Int (Int64)
import Data.List (find, intercalate)
import Data.Primitive.PrimArray qualified as P
import System.Directory.Extra (listFiles)
import System.Environment (getArgs, getProgName)
import System.FilePath (isExtensionOf, takeFileName)
import System.IO (stderr)
import Text.Printf (hPrintf, printf)

-- | The type of a generic analysis function
type EventAnalyser =
  EvaluationContext
  -> [Int64] -- cost parameters
  -> ScriptEvaluationEvent
  -> IO ()

-- Analyse values in ScriptContext

-- Script purpose: this is the same for V1 and V2, but changes in V3
stringOfPurposeV1 :: V1.ScriptPurpose -> String
stringOfPurposeV1 = \case
  V1.Minting _ -> "V1 Minting" -- Script arguments are [redeemer, context]
  V1.Spending _ -> "V1 Spending" -- Script arguments are [datum, redeemer, context]
  V1.Rewarding _ -> "V1 Rewarding" -- Script arguments appear to be [redeemer, context]
  V1.Certifying _ -> "V1 Certifying" -- Script arguments appear to be [redeemer, context]

stringOfPurposeV2 :: V2.ScriptPurpose -> String
stringOfPurposeV2 = \case
  V2.Minting _ -> "V2 Minting"
  V2.Spending _ -> "V2 Spending"
  V2.Rewarding _ -> "V2 Rewarding"
  V2.Certifying _ -> "V2 Certifying"

stringOfPurposeV3 :: V3.ScriptInfo -> String
stringOfPurposeV3 = \case
  V3.MintingScript {} -> "V3 Minting"
  V3.SpendingScript {} -> "V3 Spending"
  V3.RewardingScript {} -> "V3 Rewarding"
  V3.CertifyingScript {} -> "V3 Certifying"
  V3.VotingScript {} -> "V3 Voting"
  V3.ProposingScript {} -> "V3 Proposing"

shapeOfValue :: V1.Value -> String
shapeOfValue (V1.Value m) =
  let l = M.toList m
   in printf "[%d: %s]" (length l) (intercalate "," (fmap (printf "%d" . length . M.toList . snd) l))

analyseValue :: V1.Value -> IO ()
analyseValue v = do
  putStr $ shapeOfValue v
  printf "\n"

analyseOutputs :: [a] -> (a -> V1.Value) -> IO () -- Luckily V1.Value is the same as V2.Value
analyseOutputs outputs getValue =
  case outputs of
    [] -> putStrLn "No outputs" -- This happens in 0000000046344292-*.event
    l -> do
      putStr $ printf "Outputs %d " (length l)
      putStrLn $ intercalate ", " (fmap (shapeOfValue . getValue) l)

analyseTxInfoV1 :: V1.TxInfo -> IO ()
analyseTxInfoV1 i = do
  putStr "Fee:     "
  analyseValue $ V1.txInfoFee i
  putStr "Mint:    "
  analyseValue $ V1.txInfoMint i
  analyseOutputs (V1.txInfoOutputs i) V1.txOutValue

analyseTxInfoV2 :: V2.TxInfo -> IO ()
analyseTxInfoV2 i = do
  putStr "Fee:     "
  analyseValue $ V2.txInfoFee i
  putStr "Mint:    "
  analyseValue $ V2.txInfoMint i
  analyseOutputs (V2.txInfoOutputs i) V2.txOutValue

analyseTxInfoV3 :: V3.TxInfo -> IO ()
analyseTxInfoV3 i = do
  putStr "Fee:     "
  print $ V3.txInfoFee i
  putStr "Mint:    "
  analyseValue $ V3.mintValueMinted (V3.txInfoMint i)
  putStr "Burn:    "
  analyseValue $ V3.mintValueBurned (V3.txInfoMint i)
  analyseOutputs (V3.txInfoOutputs i) V3.txOutValue

analyseScriptContext :: EventAnalyser
analyseScriptContext _ctx _params ev = case ev of
  PlutusEvent PlutusV1 ScriptEvaluationData {..} _expected ->
    case dataInputs of
      [_, _, c] -> analyseCtxV1 c
      [_, c] -> analyseCtxV1 c
      l -> error $ printf "Unexpected number of V1 script arguments: %d" (length l)
  PlutusEvent PlutusV2 ScriptEvaluationData {..} _expected ->
    case dataInputs of
      [_, _, c] -> analyseCtxV2 c
      [_, c] -> analyseCtxV2 c
      l -> error $ printf "Unexpected number of V2 script arguments: %d" (length l)
  PlutusEvent PlutusV3 ScriptEvaluationData {..} _expected ->
    case dataInputs of
      [_, _, c] -> analyseCtxV3 c
      [_, c] -> analyseCtxV3 c
      l -> error $ printf "Unexpected number of V3 script arguments: %d" (length l)
  where
    analyseCtxV1 c =
      case V1.fromData @V1.ScriptContext c of
        Just p -> printV1info p
        Nothing -> do
          -- This really happens: there are V1 events in 0000000103367139-*.event with a V2 context
          putStrLn "\n* Failed to decode V1 ScriptContext for V1 event: trying V2"
          case V2.fromData @V2.ScriptContext c of
            Nothing -> putStrLn "* Failed to decode V2 ScriptContext for V1 event: giving up\n"
            Just p ->
              do
                putStrLn "* Successfully decoded V2 ScriptContext for V1 event"
                printV2info p

    analyseCtxV2 c =
      case V2.fromData @V2.ScriptContext c of
        Just p -> printV2info p
        Nothing -> do
          putStrLn "\n* Failed to decode V2 ScriptContext for V2 event: trying V1"
          case V1.fromData @V1.ScriptContext c of
            Nothing -> putStrLn "* Failed to decode V1 ScriptContext for V2 event: giving up\n"
            Just p ->
              do
                putStrLn "* Successfully decoded V1 ScriptContext for V2 event"
                printV1info p

    analyseCtxV3 c =
      case V3.fromData @V3.ScriptContext c of
        Just p -> printV3info p
        Nothing -> do
          putStrLn "\n* Failed to decode V3 ScriptContext for V3 event: trying V2"
          case V2.fromData @V2.ScriptContext c of
            Just p -> do
              putStrLn "* Successfully decoded V2 ScriptContext for V3 event"
              printV2info p
            Nothing -> putStrLn "* Failed to decode V3 ScriptContext for V2 event: trying V1\n"
          case V1.fromData @V1.ScriptContext c of
            Just p -> do
              putStrLn "* Successfully decoded V1 ScriptContext for V3 event"
              printV1info p
            Nothing -> putStrLn "* Failed to decode V1 ScriptContext for V3 event: giving up\n"

    printV1info p = do
      putStrLn "----------------"
      putStrLn $ stringOfPurposeV1 $ V1.scriptContextPurpose p
      analyseTxInfoV1 $ V1.scriptContextTxInfo p

    printV2info p = do
      putStrLn "----------------"
      putStrLn $ stringOfPurposeV2 $ V2.scriptContextPurpose p
      analyseTxInfoV2 $ V2.scriptContextTxInfo p

    printV3info p = do
      putStrLn "----------------"
      putStrLn $ stringOfPurposeV3 $ V3.scriptContextScriptInfo p
      analyseTxInfoV3 $ V3.scriptContextTxInfo p

-- Data object analysis

-- Statistics about a Data object
data DataInfo = DataInfo
  { _memUsage :: Integer
  , _numNodes :: Integer
  , _depth :: Integer
  , _numInodes :: Integer
  , _maxIsize :: Integer -- Maximum memoryUsage of integers in I nodes
  , _totalIsize :: Integer -- Total memoryUsage of integers in I nodes
  , _numBnodes :: Integer
  , _maxBsize :: Integer -- Maximum memoryUsage of bytestrings in B nodes
  , _totalBsize :: Integer -- Total memoryUsage of bytestrings in B nodes
  , _numLnodes :: Integer
  , _maxLlen :: Integer -- Maximum list length
  , _numCnodes :: Integer
  , _maxClen :: Integer -- Maximum number of constructor arguments
  , _numMnodes :: Integer
  , _maxMlen :: Integer -- Maximum map length
  }
  deriving stock (Show)
makeLenses ''DataInfo

emptyInfo :: DataInfo
emptyInfo = DataInfo 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

-- Memory usage as an Integer (in units of 64 bits / 8 bytes)
memU :: ExMemoryUsage a => a -> Integer
memU = fromSatInt . sumCostStream . flattenCostRose . memoryUsage

-- Header (useful for R)
printDataHeader :: IO ()
printDataHeader =
  printf "memUsage numNodes depth numI maxIsize totalIsize numB maxBsize totalBsize numL maxL numC maxC numM maxM\n"

printDataInfo :: DataInfo -> IO ()
printDataInfo DataInfo {..} =
  printf
    "%4d %4d %4d    %4d %4d %4d    %4d %4d %4d    %4d %4d   %4d %4d    %4d %4d\n"
    _memUsage
    _numNodes
    _depth
    _numInodes
    _maxIsize
    _totalIsize
    _numBnodes
    _maxBsize
    _totalBsize
    _numLnodes
    _maxLlen
    _numCnodes
    _maxClen
    _numMnodes
    _maxMlen

-- Traverse a Data object collecting information
getDataInfo :: Data -> DataInfo
getDataInfo d =
  let ilen = fromIntegral . length
      info = go d emptyInfo
      go x i =
        case x of
          I n -> i & numInodes +~ 1 & maxIsize %~ max s & totalIsize +~ s where s = memU n
          B b -> i & numBnodes +~ 1 & maxBsize %~ max s & totalBsize +~ s where s = memU b
          List l -> foldr go i' l where i' = i & numLnodes +~ 1 & maxLlen %~ max (ilen l)
          Data.Array v -> foldr go i' (Vector.toList v) where i' = i & numLnodes +~ 1 & maxLlen %~ max (ilen (Vector.toList v))
          Data.Constr _ l -> foldr go i' l where i' = i & numCnodes %~ (+ 1) & maxClen %~ max (ilen l)
          Map l ->
            let (a, b) = unzip l
             in foldr go (foldr go i' a) b
            where
              i' = i & numMnodes +~ 1 & maxMlen %~ max (ilen l)
      getDepth = \case
        I _ -> 1
        B _ -> 1
        List l -> 1 + depthList l
        Data.Array v -> 1 + depthList (Vector.toList v)
        Data.Constr _ l -> 1 + depthList l
        Map l ->
          let (a, b) = unzip l
           in 1 + max (depthList a) (depthList b)
      depthList = foldl (\n a -> max n (getDepth a)) 0
      totalNodes = sum $ info ^.. (numInodes <> numBnodes <> numLnodes <> numCnodes <> numMnodes)
   in info & memUsage .~ memU d & numNodes .~ totalNodes & depth .~ getDepth d

printDataInfoFor :: Data -> IO ()
printDataInfoFor = printDataInfo <$> getDataInfo

-- Analyse a redeemer (as a Data object) from a script evaluation event
analyseRedeemer :: EventAnalyser
analyseRedeemer _ctx _params ev = do
  case ev of
    PlutusEvent ledgerLanguage ScriptEvaluationData {..} _expected ->
      case dataInputs of
        [_d, r, _c] -> printDataInfoFor r
        [r, _c] -> printDataInfoFor r
        l -> printf "* Unexpected number of %s script arguments: %d" (show ledgerLanguage) (length l)

-- Analyse a datum (as a Data object) from a script evaluation event
analyseDatum :: EventAnalyser
analyseDatum _ctx _params ev = do
  case ev of
    PlutusEvent ledgerLanguage ScriptEvaluationData {..} _expected ->
      case dataInputs of
        [d, _r, _c] -> printDataInfoFor d
        [_r, _c] -> pure ()
        l -> printf "* Unexpected number of %s script arguments: %d" (show ledgerLanguage) (length l)

-- Print statistics about Data objects in a Term
analyseTermDataObjects :: Term NamedDeBruijn DefaultUni DefaultFun () -> IO ()
analyseTermDataObjects = go
  where
    go =
      \case
        Var _ _ -> pure ()
        LamAbs _ _ t -> go t
        Apply _ t1 t2 -> go t1 >> go t2
        Force _ t -> go t
        Delay _ t -> go t
        Constant _ c ->
          case c of
            Some (ValueOf DefaultUniData d) -> printDataInfoFor d
            _ -> pure ()
        Builtin _ _ -> pure ()
        Error _ -> pure ()
        UPLC.Constr _ _ ts -> mapM_ go ts
        Case _ t1 t2 -> go t1 >> mapM_ go t2

-- Counting builtins

type BuiltinCounts = P.MutablePrimArray (PrimState IO) Int

countBuiltinsInTerm :: BuiltinCounts -> Term NamedDeBruijn DefaultUni DefaultFun () -> IO ()
countBuiltinsInTerm counts = go
  where
    go = \case
      Var _ _ -> pure ()
      LamAbs _ _ t -> go t
      Apply _ t1 t2 -> go t1 >> go t2
      Force _ t -> go t
      Delay _ t -> go t
      Constant _ _ -> pure ()
      Builtin _ b -> incrCount $ fromEnum b
      Error _ -> pure ()
      UPLC.Constr _ _ ts -> mapM_ go ts
      Case _ t1 t2 -> go t1 >> mapM_ go t2
    incrCount i = do
      c <- P.readPrimArray counts i
      P.writePrimArray counts i (c + 1)

-- The other analyses just print out results as they proceed.  It's a little
-- more complicated here because we have to accumulate the results and print
-- them out at the end.
countBuiltins :: [FilePath] -> IO ()
countBuiltins eventFiles = do
  let numBuiltins = fromEnum (maxBound :: DefaultFun) - fromEnum (minBound :: DefaultFun) + 1
  counts :: BuiltinCounts <- P.newPrimArray numBuiltins
  P.setPrimArray counts 0 numBuiltins 0
  mapM_ (analyseOneFile (analyseUnappliedScript (countBuiltinsInTerm counts))) eventFiles
  finalCounts <- P.freezePrimArray counts 0 numBuiltins
  P.itraversePrimArray_ printEntry finalCounts
  where
    printEntry i = printf "%-35s %12d\n" (show (toEnum i :: DefaultFun))

data EvaluationResult = OK ExBudget | Failed | DeserialisationError

-- Convert to a string for use in an R frame
toRString :: EvaluationResult -> String
toRString = \case
  OK _ -> "T"
  Failed -> "F"
  DeserialisationError -> "NA"

-- Print out the actual and claimed CPU and memory cost of every script.
analyseCosts :: EventAnalyser
analyseCosts ctx _ ev =
  case ev of
    PlutusEvent PlutusV1 ScriptEvaluationData {..} _ ->
      let result =
            case deserialiseScript PlutusV1 dataProtocolVersion dataScript of
              Left _ -> DeserialisationError
              Right script ->
                case V1.evaluateScriptRestricting
                  dataProtocolVersion
                  V1.Quiet
                  ctx
                  dataBudget
                  script
                  dataInputs of
                  (_, Left _) -> Failed
                  (_, Right cost) -> OK cost
       in printCost result dataBudget
    PlutusEvent PlutusV2 ScriptEvaluationData {..} _ ->
      let result =
            case deserialiseScript PlutusV2 dataProtocolVersion dataScript of
              Left _ -> DeserialisationError
              Right script ->
                case V2.evaluateScriptRestricting
                  dataProtocolVersion
                  V2.Quiet
                  ctx
                  dataBudget
                  script
                  dataInputs of
                  (_, Left _) -> Failed
                  (_, Right cost) -> OK cost
       in printCost result dataBudget
    PlutusEvent PlutusV3 ScriptEvaluationData {..} _ -> do
      dataInput <-
        case dataInputs of
          [input] -> pure input
          _ -> throwIO $ userError "PlutusV3 script expects exactly one input"
      let result =
            case deserialiseScript PlutusV3 dataProtocolVersion dataScript of
              Left _ -> DeserialisationError
              Right script -> do
                case V3.evaluateScriptRestricting
                  dataProtocolVersion
                  V3.Quiet
                  ctx
                  dataBudget
                  script
                  dataInput of
                  (_, Left _) -> Failed
                  (_, Right cost) -> OK cost
      printCost result dataBudget
  where
    printCost :: EvaluationResult -> ExBudget -> IO ()
    printCost result claimedCost =
      let (claimedCPU, claimedMem) = costAsInts claimedCost
       in case result of
            OK cost ->
              let (actualCPU, actualMem) = costAsInts cost
               in printf "%15d   %15d   %15d   %15d      %2s\n" actualCPU claimedCPU actualMem claimedMem (toRString result)
            -- Something went wrong; print the cost as "NA" ("Not Available" in R) so that R can
            -- still process it.
            _ ->
              printf "%15s   %15d   %15s   %15d      %2s\n" "NA" claimedCPU "NA" claimedMem (toRString result)
    costAsInts :: ExBudget -> (Int, Int)
    costAsInts (ExBudget (V2.ExCPU cpu) (V2.ExMemory mem)) =
      (fromSatInt cpu, fromSatInt mem)

-- Extract the script from an evaluation event and apply some analysis function
analyseUnappliedScript :: (Term NamedDeBruijn DefaultUni DefaultFun () -> IO ()) -> EventAnalyser
analyseUnappliedScript
  analyse
  _ctx
  _params
  (PlutusEvent plutusLedgerLanguage ScriptEvaluationData {..} _expected) =
    case deserialiseScript plutusLedgerLanguage dataProtocolVersion dataScript of
      Left err -> print err
      Right (deserialisedScript -> ScriptNamedDeBruijn (Program _ _ t)) -> analyse t

-- | Run some analysis function over the events from a single event dump file
analyseOneFile
  :: EventAnalyser
  -> FilePath
  -> IO ()
analyseOneFile analyse eventFile = do
  events <- loadEvents eventFile
  printf "# %s\n" $ takeFileName eventFile
  -- Print the file in the output so we can narrow down the location of
  -- interesting/anomalous data.  This may not be helpful for some of the
  -- analyses.
  case ( mkContext V1.mkEvaluationContext (eventsCostParamsV1 events)
       , mkContext V2.mkEvaluationContext (eventsCostParamsV2 events)
       , mkContext V3.mkEvaluationContext (eventsCostParamsV2 events)
       ) of
    (Right ctxV1, Right ctxV2, Right ctxV3) ->
      mapM_ (runSingleEvent ctxV1 ctxV2 ctxV3) (eventsOf events)
    (Left err, _, _) -> error $ display err
    (_, Left err, _) -> error $ display err
    (_, _, Left err) -> error $ display err
  where
    mkContext f = \case
      Nothing -> Right Nothing
      Just costParams -> Just . (,costParams) . fst <$> runWriterT (f costParams)

    runSingleEvent
      :: Maybe (EvaluationContext, [Int64])
      -> Maybe (EvaluationContext, [Int64])
      -> Maybe (EvaluationContext, [Int64])
      -> ScriptEvaluationEvent
      -> IO ()
    runSingleEvent ctxV1 ctxV2 ctxV3 event =
      case event of
        PlutusEvent PlutusV1 _ _ ->
          case ctxV1 of
            Just (ctx, params) -> analyse ctx params event
            Nothing -> putStrLn "*** ctxV1 missing ***"
        PlutusEvent PlutusV2 _ _ ->
          case ctxV2 of
            Just (ctx, params) -> analyse ctx params event
            Nothing -> putStrLn "*** ctxV2 missing ***"
        PlutusEvent PlutusV3 _ _ ->
          case ctxV3 of
            Just (ctx, params) -> analyse ctx params event
            Nothing -> putStrLn "*** ctxV3 missing ***"

main :: IO ()
main =
  let analyses =
        [
          ( "values"
          , "analyse shapes of Values"
          , doAnalysis analyseScriptContext
          )
        ,
          ( "redeemers"
          , "print statistics about redeemer Data objects"
          , printDataHeader `thenDoAnalysis` analyseRedeemer
          )
        ,
          ( "datums"
          , "print statistics about datum Data objects"
          , printDataHeader `thenDoAnalysis` analyseDatum
          )
        ,
          ( "script-data"
          , "print statistics about Data objects in validator scripts"
          , printDataHeader `thenDoAnalysis` analyseUnappliedScript analyseTermDataObjects
          )
        ,
          ( "count-builtins"
          , "count the total number of occurrences of each builtin in validator scripts"
          , countBuiltins
          )
        ,
          ( "costs"
          , "print actual and claimed costs of scripts"
          , putStrLn "      cpuActual        cpuClaimed         memActual         memClaimed   status"
              `thenDoAnalysis` analyseCosts
          )
        ]

      doAnalysis analyser = mapM_ (analyseOneFile analyser)
      (prelude `thenDoAnalysis` analyser) files = prelude >> doAnalysis analyser files

      usage = do
        getProgName >>= hPrintf stderr "Usage: %s <analysis> [<dir>]\n"
        hPrintf stderr "Analyse the .event files in <dir> (default = current directory)\n"
        hPrintf stderr "Avaliable analyses:\n"
        mapM_ printDescription analyses
        where
          printDescription (n, h, _) = hPrintf stderr "   %-16s: %s\n" n h

      go name dir =
        case find (\(n, _, _) -> n == name) analyses of
          Nothing -> printf "Unknown analysis: %s\n" name >> usage
          Just (_, _, analysis) -> do
            files <- listFiles dir
            case filter ("event" `isExtensionOf`) files of
              [] -> printf "No .event files in %s\n" dir
              eventFiles -> analysis eventFiles
   in getArgs >>= \case
        [name] -> go name "."
        [name, dir] -> go name dir
        _ -> usage
