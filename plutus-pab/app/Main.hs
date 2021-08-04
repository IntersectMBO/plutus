{-# LANGUAGE ApplicativeDo         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Main
    ( main
    ) where

import           CommandParser        (AppOpts (..), parseOptions)
import           Plutus.PAB.Run.Cli   (runNoConfigCommand)

import           Control.Monad.Logger (logErrorN, runStdoutLoggingT)
import           Data.Text.Extras     (tshow)
import           Plutus.PAB.Types     (PABError)
import           System.Exit          (ExitCode (ExitFailure), exitSuccess, exitWith)

main :: IO ()
main = do
    AppOpts { cmd } <- parseOptions

    -- execute parsed pab command and handle errors on failure
    result <- Right <$> runNoConfigCommand cmd
    either handleError (const exitSuccess) result

    where
        handleError (err :: PABError) = do
            runStdoutLoggingT $ (logErrorN . tshow) err
            exitWith (ExitFailure 1)
