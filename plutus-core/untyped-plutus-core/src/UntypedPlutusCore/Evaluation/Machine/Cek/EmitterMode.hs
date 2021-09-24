{-# LANGUAGE OverloadedStrings #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.EmitterMode (noEmitter, logEmitter, logWithTimeEmitter, logWithBudgetEmitter) where

import           UntypedPlutusCore.Evaluation.Machine.Cek.Internal

import           Control.Monad.ST.Unsafe                           (unsafeIOToST)
import qualified Data.DList                                        as DList
import           Data.STRef                                        (modifySTRef, newSTRef, readSTRef)
import           Data.Text                                         (pack)
import           Data.Time.Clock                                   (getCurrentTime)
import           PlutusCore.Evaluation.Machine.ExBudget
import           Prettyprinter

-- | No emitter.
noEmitter :: EmitterMode uni fun
noEmitter = EmitterMode $ \_ -> pure $ CekEmitterInfo (\_ -> pure ()) (pure mempty)

-- | Emits log only.
logEmitter :: EmitterMode uni fun
logEmitter = EmitterMode $ \_ -> do
    logsRef <- newSTRef DList.empty
    let emitter str = CekM $ modifySTRef logsRef (`DList.snoc` str)
    pure $ CekEmitterInfo emitter (DList.toList <$> readSTRef logsRef)

-- | Emits log with timestamp.
logWithTimeEmitter :: EmitterMode uni fun
logWithTimeEmitter = EmitterMode $ \_ -> do
    logsRef <- newSTRef DList.empty
    let emitter str = CekM $ do
            time <- unsafeIOToST getCurrentTime
            let withTime = brackets (viaShow time) <+> pretty str
            modifySTRef logsRef (`DList.snoc` (pack $ show withTime))
    pure $ CekEmitterInfo emitter (DList.toList <$> readSTRef logsRef)

-- | Emits log with the budget.
logWithBudgetEmitter :: EmitterMode uni fun
logWithBudgetEmitter = EmitterMode $ \getBudget -> do
    logsRef <- newSTRef DList.empty
    let emitter str = CekM $ do
            ExBudget exCpu exMemory <- getBudget
            let withBudget = brackets (pretty exCpu <> "," <> pretty exMemory) <+> pretty str
            modifySTRef logsRef (`DList.snoc` (pack $ show withBudget))
    pure $ CekEmitterInfo emitter (DList.toList <$> readSTRef logsRef)
