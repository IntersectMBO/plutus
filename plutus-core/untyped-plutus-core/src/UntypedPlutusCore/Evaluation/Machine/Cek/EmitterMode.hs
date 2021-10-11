{-# LANGUAGE OverloadedStrings #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.EmitterMode (noEmitter, logEmitter, logWithTimeEmitter) where

import           UntypedPlutusCore.Evaluation.Machine.Cek.Internal

import           Control.Monad.ST.Unsafe                           (unsafeIOToST)
import qualified Data.DList                                        as DList
import           Data.STRef                                        (modifySTRef, newSTRef, readSTRef)
import           Data.Text                                         (pack)
import           Data.Time.Clock                                   (getCurrentTime)

-- | No emitter.
noEmitter :: EmitterMode uni fun
noEmitter = EmitterMode $ pure $ CekEmitterInfo (\_ -> pure ()) (pure mempty)

-- | Emits log only.
logEmitter :: EmitterMode uni fun
logEmitter = EmitterMode $ do
    logsRef <- newSTRef DList.empty
    let emitter str = CekM $ modifySTRef logsRef (`DList.snoc` str)
    pure $ CekEmitterInfo emitter (DList.toList <$> readSTRef logsRef)

-- | Emits log with timestamp.
logWithTimeEmitter :: EmitterMode uni fun
logWithTimeEmitter = EmitterMode $ do
    logsRef <- newSTRef DList.empty
    let emitter str = CekM $ do
            time <- unsafeIOToST getCurrentTime
            let withTime = pack (show time) <> " " <> str
            modifySTRef logsRef (`DList.snoc` withTime)
    pure $ CekEmitterInfo emitter (DList.toList <$> readSTRef logsRef)
