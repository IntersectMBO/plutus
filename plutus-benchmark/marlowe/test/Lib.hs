{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Lib where

import Control.Exception (throwIO)
import Control.Monad.Except (runExceptT)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text.IO
import Formatting qualified as F
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Evaluation.Machine.ExMemory (CostingInteger)
import PlutusCore.Test (runUPlcFull)
import PlutusLedgerApi.V3 (ExBudget (..), ExCPU (..), ExMemory (..), fromSatInt)
import System.Directory (createDirectoryIfMissing, removeFile)
import System.FilePath qualified as Path
import System.IO (Handle, IOMode (WriteMode), withFile)
import Test.Tasty (TestName, TestTree)
import Test.Tasty.Golden.Advanced (goldenTest2)
import Text.Read (readMaybe)
import Text.Tabular (Header (..), Properties (NoLine, SingleLine), Table (Table))
import Text.Tabular.AsciiArt qualified as Tabular
import UntypedPlutusCore (NamedDeBruijn)
import UntypedPlutusCore.AstSize qualified as UPLC
import UntypedPlutusCore.Core.Type qualified as UPLC

-- | Measure the given program's execution budget and size.
measureProgram
  :: UPLC.Program NamedDeBruijn DefaultUni DefaultFun ()
  -> IO (ExCPU, ExMemory, UPLC.AstSize)
measureProgram program =
  runExceptT (runUPlcFull [program]) >>= \case
    Left err -> fail $ "Error evaluating UPLC program: " <> show err
    Right (_term, ExBudget exCpu exMem, _logs) ->
      pure (exCpu, exMem, UPLC.programAstSize program)

{-| Compare the output file's contents against the golden file's contents
after the given action has created the output file. -}
goldenUplcMeasurements
  :: TestName
  -- ^ test name
  -> FilePath
  -- ^ path to the «golden» file (the file that contains correct output)
  -> FilePath
  -- ^ path to the output file
  -> (Handle -> IO ())
  -- ^ Given a file handle, action that writes measurements to it.
  -> TestTree
  {-^ the test verifies that the output file contents is the same as
  the golden file contents -}
goldenUplcMeasurements name goldenPath outputPath act =
  goldenTest2
    name
    (Text.IO.readFile goldenPath)
    (withFile outputPath WriteMode act >> Text.IO.readFile outputPath)
    reportDifference
    (createDirectoriesAndWriteFile goldenPath)
    (removeFile outputPath)
  where
    reportDifference :: Text -> Text -> IO (Maybe String)
    reportDifference expected actual = do
      let parse = traverse parseLine . Text.lines
      expectedResults <- parse expected
      actualResults <- parse actual
      if expectedResults == actualResults
        then pure Nothing
        else do
          let (cpu0, mem0, size0) = aggregateResults expectedResults
              (cpu1, mem1, size1) = aggregateResults actualResults

          pure . Just $
            "Actual execution budgets and sizes differ from expected ones:\n"
              <> Tabular.render
                id
                id
                Text.unpack
                ( Table
                    ( Group
                        NoLine
                        [ Header "Baseline (average)"
                        , Header "Actual (average)"
                        , Header "Delta"
                        ]
                    )
                    ( Group
                        SingleLine
                        [ Header "CPU units"
                        , Header "Memory units"
                        , Header "AST Size"
                        ]
                    )
                    [ [formatUnits cpu0, formatUnits mem0, formatUnits size0]
                    , [formatUnits cpu1, formatUnits mem1, formatUnits size1]
                    ,
                      [ formatDelta cpu1 cpu0
                      , formatDelta mem1 mem0
                      , formatDelta size1 size0
                      ]
                    ]
                )

aggregateResults
  :: [(ExCPU, ExMemory, UPLC.AstSize)]
  -> (Integer, Integer, Integer)
aggregateResults results =
  ( average (map (\(ExCPU i) -> fromSatInt i) cpus)
  , average (map (\(ExMemory m) -> fromSatInt m) mems)
  , average (map UPLC.unAstSize sizes)
  )
  where
    (cpus, mems, sizes) = unzip3 results
    average xs
      | null xs = 0
      | otherwise = sum xs `div` fromIntegral (length xs)

formatDelta :: Integer -> Integer -> Text
formatDelta a b = F.sformat (F.fixed 2 F.% "%") (delta b a)
  where
    delta :: Integer -> Integer -> Double
    delta x y
      | x > 0 = (fromIntegral (y - x) * 100) / fromIntegral x
      | otherwise = 0

formatUnits :: Integer -> Text
formatUnits = F.sformat (F.groupInt 3 ' ')

-- | Like 'writeFile', but also create parent dirs if they are missing.
createDirectoriesAndWriteFile :: FilePath -> Text -> IO ()
createDirectoriesAndWriteFile path bs = do
  let dir = Path.takeDirectory path
  createDirectoryIfMissing
    True -- create parents too
    dir
  Text.IO.writeFile path bs

parseLine :: Text -> IO (ExCPU, ExMemory, UPLC.AstSize)
parseLine ln =
  case Text.splitOn "\t" ln of
    [cpu, mem, size] ->
      (,,)
        <$> readCpu cpu
        <*> readMem mem
        <*> readAstSize size
    _ -> throwIO . userError $ "Can't parse line: " <> show ln
  where
    readCpu :: Text -> IO ExCPU
    readCpu t =
      case readMaybe (Text.unpack t) of
        Just (cpu :: CostingInteger) -> pure (ExCPU cpu)
        Nothing ->
          throwIO . userError $ "Can't parse CPU exec units: " <> show t

    readMem :: Text -> IO ExMemory
    readMem t =
      case readMaybe (Text.unpack t) of
        Just (mem :: CostingInteger) -> pure (ExMemory mem)
        Nothing ->
          throwIO . userError $ "Can't parse Memory exec units: " <> show t

    readAstSize :: Text -> IO UPLC.AstSize
    readAstSize t =
      case readMaybe (Text.unpack t) of
        Just (size :: Integer) -> pure (UPLC.AstSize size)
        Nothing ->
          throwIO . userError $ "Can't parse program size: " <> show t
