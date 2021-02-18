{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}

module Control.Monad.Freer.Extra.Log(
    -- $log
    LogMsg
    , logDebug
    , logInfo
    , logWarn
    , handleWriterLog
    ) where

import           Control.Monad.Freer.Log (LogMsg (..), handleWriterLog, logDebug, logInfo, logWarn)
