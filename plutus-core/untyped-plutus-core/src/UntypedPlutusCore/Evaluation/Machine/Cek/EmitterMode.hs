{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.EmitterMode (
  noEmitter,
  logEmitter,
  logWithTimeEmitter,
  logWithBudgetEmitter,
  logWithCallTraceEmitter,
) where

import UntypedPlutusCore.Evaluation.Machine.Cek.Internal

import Control.Monad.ST.Unsafe (unsafeIOToST)
import Data.ByteString.Builder qualified as BS
import Data.ByteString.Lazy qualified as BSL
import Data.Csv qualified as CSV
import Data.Csv.Builder qualified as CSV
import Data.DList qualified as DList
import Data.Fixed
import Data.Functor
import Data.SatInt
import Data.STRef (modifySTRef, newSTRef, readSTRef)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Time.Clock
import Data.Time.Clock.POSIX
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExMemory

-- | No emitter.
noEmitter :: EmitterMode uni fun
noEmitter = EmitterMode $ \_ -> pure $ CekEmitterInfo (\_ -> pure ()) (pure mempty)

-- | Emits log only.
logEmitter :: EmitterMode uni fun
logEmitter = EmitterMode $ \_ -> do
  logsRef <- newSTRef DList.empty
  let emitter logs = CekM $ modifySTRef logsRef (`DList.append` logs)
  pure $ CekEmitterInfo emitter (DList.toList <$> readSTRef logsRef)

-- A wrapper around encoding a record. `cassava` insists on including a trailing newline, which is
-- annoying since we're recording the output line-by-line.
encodeRecord :: (CSV.ToRecord a) => a -> T.Text
encodeRecord a = T.stripEnd $ T.decodeUtf8 $ BSL.toStrict $ BS.toLazyByteString $ CSV.encodeRecord a

-- | Emits log with timestamp.
logWithTimeEmitter :: EmitterMode uni fun
logWithTimeEmitter = EmitterMode $ \_ -> do
  logsRef <- newSTRef DList.empty
  let emitter logs = CekM $ do
        time <- unsafeIOToST getCurrentTime
        let secs = let MkFixed s = nominalDiffTimeToSeconds $ utcTimeToPOSIXSeconds time in s
        let withTime = logs <&> \str -> encodeRecord (str, secs)
        modifySTRef logsRef (`DList.append` withTime)
  pure $ CekEmitterInfo emitter (DList.toList <$> readSTRef logsRef)

instance CSV.ToField ExCPU where
  toField (ExCPU t) = CSV.toField $ unSatInt t

instance CSV.ToField ExMemory where
  toField (ExMemory t) = CSV.toField $ unSatInt t

-- | Emits log with the budget.
logWithBudgetEmitter :: EmitterMode uni fun
logWithBudgetEmitter = EmitterMode $ \getBudget -> do
  logsRef <- newSTRef DList.empty
  let emitter logs = CekM $ do
        ExBudget exCpu exMemory <- getBudget
        let withBudget = logs <&> \str -> encodeRecord (str, exCpu, exMemory)
        modifySTRef logsRef (`DList.append` withBudget)
  pure $ CekEmitterInfo emitter (DList.toList <$> readSTRef logsRef)

{-| Emits log and, when script evaluation fails, call trace.

This requires script to be compiled with `PlutusTx.Plugin:profile-all` turned on because this relies
on compiler-generated trace calls that notifies entrance and exit of a function call. These traces
that mark entrance and exit are ordinary traces like "-> rob:Example.hs:3:1-3:15" and "<-
bob:Example.hs:1:1-1:13" with "->" and "<-" prefixies, where "bob" and "rob" is the name
of the function with source span. If regular script with no entrance/exit marker is given, this
emitter will behave identically to 'logEmitter'.

When script evaluation fails, this emitter will give call trace of the functions that led to the
evaluation failure.  This is useful for pin-pointing specific area of the codebase that caused
failure when debugging a script. When script evaluation passes, every trace message generated by
`profile-all` flag will be removed, and this emitter will behave identically to 'logEmitter'.
-}
logWithCallTraceEmitter :: EmitterMode uni fun
logWithCallTraceEmitter = EmitterMode $ \_ -> do
  logsRef <- newSTRef DList.empty
  let
    addTrace DList.Nil logs = logs
    addTrace newLogs DList.Nil = newLogs
    addTrace newLogs logs = DList.fromList $ go (DList.toList newLogs) (DList.toList logs)
     where
      go l [] = l
      go [] l = l
      go (x : xs) l =
        -- See Note [Profiling Marker]
        case (T.words (last l), T.words x) of
          ("->" : enterRest, "<-" : exitRest) | enterRest == exitRest -> go xs (init l)
          _                                                           -> go xs (l <> [x])

    emitter logs = CekM $ modifySTRef logsRef (addTrace logs)
  pure $ CekEmitterInfo emitter (DList.toList <$> readSTRef logsRef)
