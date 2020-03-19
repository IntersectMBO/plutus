{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

import           Data.Functor            (void)
import           Data.Semigroup          ((<>))

import           Control.Concurrent      (forkIO, newMVar, readMVar, threadDelay)
import           Control.Concurrent.STM
import           Control.Lens            (view)
import           Control.Monad           (forever, when)
import           Control.Monad.IO.Class  (liftIO)
import           Control.Monad.Logger
import           Control.Monad.Reader

import           Options.Applicative     (Parser, ParserInfo, argument, auto, execParser, fullDesc, help, helper, info,
                                          long, metavar, option, progDesc, short, str, switch, value, (<**>))

import           Cardano.Node.RandomTx
import           Cardano.Protocol.Socket.Client
import           Cardano.Protocol.Socket.Type
import           Plutus.SCB.Core
import           Plutus.SCB.Types

import           Data.Yaml               (decodeFileThrow)

-- Parsing options.
data Options = Options
  { optSocket           :: String
  , optSlotInterval     :: Int
  , optRandomTxInterval :: Int
  , optStreamEvents     :: Bool
  }

parseSocket :: Parser String
parseSocket = argument str (metavar "SOCKET")

parseSlotInterval :: Parser Int
parseSlotInterval = option auto
                    (  long    "next-slot"
                    <> short   'n'
                    <> metavar "INT"
                    <> value   0
                    <> help    "Interval in seconds until the next slot is generated, use 0 for disabling." )

parseRandomTxInterval :: Parser Int
parseRandomTxInterval = option auto
                        (  long    "tx-interval"
                        <> short   'i'
                        <> metavar "INT"
                        <> value   0
                        <> help    "Interval in seconds until a random tx is injected, use 0 for disabling." )

parseStreamEvents :: Parser Bool
parseStreamEvents = switch
                    (  long "stream"
                    <> short 's'
                    <> help  "Stream events from the node server." )

parseOptions :: Parser Options
parseOptions = Options <$> parseSocket
                       <*> parseSlotInterval
                       <*> parseRandomTxInterval
                       <*> parseStreamEvents

optParser :: ParserInfo Options
optParser = info (parseOptions <**> helper)
  (  fullDesc
  <> progDesc "Node client simulator and testing driver." )

-- Running everything.
main :: IO ()
main = do
  options <- execParser optParser
  localStateM <- newMVar emptyClientState
  config <- liftIO $ decodeFileThrow "plutus-scb.yaml"
  connection <-
      runStdoutLoggingT
    $ runReaderT dbConnect (dbConfig config)
  puppetH <- newPuppetHandle

  -- update state using event log.
  void . forkIO . forever $
      runStdoutLoggingT
    $ runReaderT (localStateRefresh 5 localStateM) connection

  when (optSlotInterval options > 0) . void . forkIO . forever $ do
    atomically  $ writeTQueue (ctlRequest puppetH) RequestValidation
    threadDelay $ optSlotInterval options * 1000000

  when (optRandomTxInterval options > 0) . void . forkIO . forever $ do
    localState <- readMVar localStateM
    tx         <- generateRandomTx (view  csIndex localState)
    atomically  $ writeTQueue (txInputQueue puppetH) tx
    threadDelay $ optRandomTxInterval options * 1000000

  when (optStreamEvents options) $
    startClientNode "sock" connection localStateM puppetH
