{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Concurrent             (threadDelay)
import           Control.Monad                  (forever)
import           Data.Either.Combinators        (maybeToRight)
import           Data.List                      (elemIndex)
import           Data.Proxy                     (Proxy (Proxy))
import           Data.Text                      (pack)
import           Data.Text.Encoding             (encodeUtf8)
import           Options.Applicative
import           Text.Read                      (readEither)

import           Cardano.Api                    (Block (..), BlockHeader (..), BlockInMode (..), ChainPoint (..),
                                                 HasTypeProxy (..), deserialiseFromRawBytesHex,
                                                 serialiseToRawBytesHexText)
import           Cardano.Protocol.Socket.Client (ChainSyncEvent (..), runChainSync)
import           Cardano.Slotting.Slot          (SlotNo (..))
import           Ledger                         (Slot)
import           Ledger.TimeSlot                (SlotConfig (..))

-- | We only need to know the location of the socket.
--   We can get the protocol versions from Cardano.Protocol.Socket.Type
data Configuration = Configuration
  { cSocketPath :: !String
  , cResumeHash :: !ChainPoint
  } deriving (Show)

-- | This is the slot configuration for the shelley network, taken from the PAB
-- configuration file.
slotConfig :: SlotConfig
slotConfig =
  SlotConfig
    { scZeroSlotTime = 1591566291000
    , scSlotLength   = 1
    }

-- | A simple callback that reads the incoming data, from the node.
processBlock
  :: ChainSyncEvent
  -> Slot
  -> IO ()
processBlock (RollForward (BlockInMode (Block (BlockHeader (SlotNo slot) hsh _) _) _)) _ =
  putStrLn $ "Received block " <> show (serialiseToRawBytesHexText hsh)
          <> " for slot "      <> show slot
processBlock (Resume (ChainPoint (SlotNo slot) hsh)) _ =
  putStrLn $ "Resuming from slot " <> show slot
          <> " at hash " <> show (serialiseToRawBytesHexText hsh)
processBlock (Resume ChainPointAtGenesis) _ =
  putStrLn "Resuming from genesis block"

hashParser :: ReadM ChainPoint
hashParser = eitherReader $
  \chainPoint -> do
    idx <- maybeToRight ("Failed to parse chain point specification. The format" <>
                         "should be HASH,SLOT")
                        (elemIndex ',' chainPoint)
    let (hash, slot') = splitAt idx chainPoint
    slot <- readEither (drop 1 slot')
    hsh  <- maybeToRight ("Failed to parse hash " <> hash) $
                         deserialiseFromRawBytesHex
                           (proxyToAsType Proxy)
                           (encodeUtf8 $ pack hash)
    pure $ ChainPoint (SlotNo slot) hsh

cfgParser :: Parser Configuration
cfgParser = Configuration
  <$> argument str (metavar "SOCKET")
  <*> option hashParser
      (  short 'r'
      <> metavar "HASH,SLOT"
      <> help "Specify the hash and the slot where we want to start synchronisation"
      <> value ChainPointAtGenesis )

main :: IO ()
main = do
  cfg <- execParser $ info (cfgParser <**> helper)
                        ( fullDesc
                        <> progDesc "Connect and stream blocks from the node client"
                        )
  putStrLn "Runtime configuration:"
  putStrLn "----------------------"
  print    cfg
  _ <- runChainSync (cSocketPath cfg)
                    slotConfig
                    [(cResumeHash cfg)]
                    processBlock
  _ <- forever $ threadDelay 1000000
  pure ()
