module SimplePlugin (plugin) where

import Control.Concurrent
import GHC.Plugins

-- | A very simple GHC plugin that just logs a message during compilation.
plugin :: Plugin
plugin =
  defaultPlugin
    { installCoreToDos = \_ todos -> do
        let getBool = do
              liftIO $ threadDelay 1000000
              return True

        b <-
          {-# SCC "XXXXxXXXXXXXXXX" #-}
          getBool
        putMsgS ("I got a bool from the plugin -> " ++ show b)
        pure todos
    , pluginRecompile = purePlugin
    }
