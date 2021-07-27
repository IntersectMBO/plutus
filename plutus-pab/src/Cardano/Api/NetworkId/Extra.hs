{-# LANGUAGE OverloadedStrings #-}

module Cardano.Api.NetworkId.Extra where

import           Cardano.Api    (NetworkId (..), NetworkMagic (..))
import           Data.Aeson     (FromJSON, ToJSON, Value (String), parseJSON, toJSON, withText)
import qualified Data.Text      as Text
import qualified Data.Text.Read as Text

-- | Wrapper for 'NetworkId' to prevent the creation of orphan instances.
newtype NetworkIdWrapper = NetworkIdWrapper { unNetworkIdWrapper :: NetworkId }
    deriving (Show, Eq)

-- | Custom 'FromJSON' instance for 'NetworkId' needed for allowing a user to
-- specify it in the 'Cardano.Node.Types.MockServerConfig'.
--
-- This instance parses 'NetworkId' as a string value. An empty string
-- refers to the Mainnet. A number encoded as a string refers to the
-- 'NetworkMagic' of the Testnet.
--
-- Here are some examples:
--
-- >>> decode "\"\"" :: Maybe NetworkId
-- Just Mainnet
--
-- >>> decode "\"1\"" :: Maybe NetworkId
-- Just (Testnet (NetworkMagic 1)))
--
-- >>> decode "\"1a\"" :: Maybe NetworkId
-- Nothing
--
-- >>> decode "\"other\"" :: Maybe NetworkId
-- Nothing
instance FromJSON NetworkIdWrapper where
    parseJSON =
        let f s = case s of
                "" -> pure $ NetworkIdWrapper Mainnet
                n -> do
                    case Text.decimal n of
                      Left errMsg    -> fail $ "parsing NetworkId failed: " <> errMsg
                      Right (n', "") -> pure $ NetworkIdWrapper $ Testnet $ NetworkMagic n'
                      Right _        -> fail "parsing NetworkId failed: the String value should contain only numbers"
         in withText "NetworkId" f

instance ToJSON NetworkIdWrapper where
    toJSON (NetworkIdWrapper Mainnet)                    = String ""
    toJSON (NetworkIdWrapper (Testnet (NetworkMagic n))) = String $ Text.pack $ show n
