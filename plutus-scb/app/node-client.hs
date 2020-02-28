{-# LANGUAGE NamedFieldPuns #-}
module Main where

import           Data.Functor             (void)
import           Data.Semigroup           ((<>))

import           Control.Concurrent       (forkIO, newMVar, readMVar, threadDelay)
import           Control.Concurrent.STM
import           Control.Lens             (view)
import           Control.Monad            (forever, when)
import           Control.Monad.IO.Class   (liftIO)
import           Control.Monad.Logger
import           Control.Monad.Reader

import           Options.Applicative      (Parser, ParserInfo, argument, auto, execParser, fullDesc, help, helper, info,
                                           long, metavar, option, progDesc, short, str, switch, value, (<**>))

import           Cardano.Node.RandomTx
import           Cardano.Protocol.Client
import           Cardano.Protocol.Type
import           Plutus.SCB.Core
import           Plutus.SCB.Types

import           Data.Yaml                (decodeFileThrow)

import           Debug.Trace

-- Parsing options.
data Options = Options
  { optSocket           :: String
  , optSlotInterval     :: Int
  , optRandomTxInterval :: Int
--  , optRandomTxCount    :: Int
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

parseRandomTxCount :: Parser Int
parseRandomTxCount = option auto
                     (  long    "tx-count"
                     <> short   'c'
                     <> metavar "INT"
                     <> value   0
                     <> help    "The count of transactions to be generated on startup." )

parseStreamEvents :: Parser Bool
parseStreamEvents = switch
                    (  long "stream"
                    <> short 's'
                    <> help  "Stream events from the node server." )

parseOptions :: Parser Options
parseOptions = Options <$> parseSocket
                       <*> parseSlotInterval
                       <*> parseRandomTxInterval
--                       <*> parseRandomTxCount
                       <*> parseStreamEvents

optParser :: ParserInfo Options
optParser = info (parseOptions <**> helper)
  (  fullDesc
  <> progDesc "Node client simulator and testing driver." )

-- Running everything.
main :: IO ()
main =
  execParser optParser >>= runClient

runClient :: Options -> IO ()
runClient Options { optSlotInterval
                  , optRandomTxInterval
--                  , optRandomTxCount
                  , optStreamEvents } = do
  config  <- liftIO $ decodeFileThrow "plutus-scb.yaml"
  connection <- runStdoutLoggingT $ runReaderT dbConnect (dbConfig config)
  chState <- (runMonadEventStore connection $
    runGlobalQuery localClientState) >>= newMVar
  cc <- readMVar chState
  puppetH <- trace ("recovered state: " ++ show cc) newPuppetHandle
  when (optSlotInterval > 0) $ void $ forkIO $ forever $ do
    threadDelay $ optSlotInterval * 1000000
    atomically  $ writeTQueue (ctlRequest puppetH) RequestValidation
  when (optRandomTxInterval > 0) $ void $ forkIO $ forever $ do
    threadDelay $ optRandomTxInterval * 1000000
    chState' <- readMVar chState
    tx <- generateRandomTx (view csIndex chState')
    atomically $ writeTQueue (txInputQueue puppetH) tx
  when optStreamEvents $
    startClientNode "sock" connection chState puppetH
