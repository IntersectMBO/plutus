-- |
-- Module      : Foundation.Timing.Main
-- License     : BSD-style
-- Maintainer  : Foundation maintainers
--
-- An implementation of a timing framework
--
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
module Foundation.Timing.Main
    ( defaultMain
    ) where

import           Basement.Imports
import           Foundation.IO.Terminal
import           Foundation.Collection

data MainConfig = MainConfig
    { mainHelp       :: Bool
    , mainListBenchs :: Bool
    , mainVerbose    :: Bool
    , mainOther      :: [String]
    }

newtype TimingPlan a = TimingPlan { runTimingPlan :: IO a }
    deriving (Functor, Applicative, Monad)

defaultMainConfig :: MainConfig
defaultMainConfig = MainConfig
    { mainHelp       = False
    , mainListBenchs = False
    , mainVerbose    = False
    , mainOther      = []
    }

parseArgs :: [String] -> MainConfig -> Either String MainConfig
parseArgs []                cfg    = Right cfg
parseArgs ("--list-benchs":xs) cfg = parseArgs xs $ cfg { mainListBenchs = True }
parseArgs ("--verbose":xs) cfg     = parseArgs xs $ cfg { mainVerbose = True }
parseArgs ("--help":xs)    cfg     = parseArgs xs $ cfg { mainHelp = True }
parseArgs (x:xs)           cfg     = parseArgs xs $ cfg { mainOther = x : mainOther cfg }

configHelp :: [String]
configHelp = []

defaultMain :: TimingPlan () -> IO ()
defaultMain tp = do
    ecfg <- flip parseArgs defaultMainConfig <$> getArgs
    cfg  <- case ecfg of
            Left e  -> do
                putStrLn e
                mapM_ putStrLn configHelp
                exitFailure
            Right c -> pure c

    when (mainHelp cfg) (mapM_ putStrLn configHelp >> exitSuccess)
    when (mainListBenchs cfg) (printAll >> exitSuccess)

    runTimingPlan tp

    return ()
  where
    printAll = undefined
