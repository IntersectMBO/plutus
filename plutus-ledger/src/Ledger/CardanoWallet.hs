{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}

{- Cardano wallet implementation for the emulator.
-}
module Ledger.CardanoWallet(
    MockWallet(..),
    -- * Enumerating wallets
    WalletNumber(..),
    fromWalletNumber,
    toWalletNumber,
    knownWallets,
    knownWallet,
    fromSeed,
    -- ** Keys
    privateKey,
    pubKeyHash,
    pubKey
    ) where

import           Cardano.Address.Derivation     (XPrv)
import qualified Cardano.Crypto.Wallet          as Crypto
import qualified Cardano.Wallet.Primitive.Types as CW
import           Codec.Serialise                (serialise)
import qualified Crypto.Hash                    as Crypto
import           Data.Aeson                     (FromJSON, ToJSON)
import           Data.Aeson.Extras              (encodeByteString)
import qualified Data.ByteString                as BS
import qualified Data.ByteString.Lazy           as BSL
import           Data.Hashable                  (Hashable (..))
import           Data.List                      (findIndex)
import           Data.Maybe                     (fromMaybe)
import qualified Data.Text                      as T
import           GHC.Generics                   (Generic)
import           Ledger.Crypto                  (PrivateKey, PubKey (..), PubKeyHash (..))
import qualified Ledger.Crypto                  as Crypto
import           Plutus.V1.Ledger.Bytes         (LedgerBytes (..))
import           Servant.API                    (FromHttpApiData (..), ToHttpApiData (..))

newtype MockPrivateKey = MockPrivateKey { unMockPrivateKey :: XPrv }

instance Show MockPrivateKey where
    show = T.unpack . encodeByteString . Crypto.unXPrv . unMockPrivateKey
instance Eq MockPrivateKey where
    (MockPrivateKey l) == (MockPrivateKey r) = Crypto.unXPrv l == Crypto.unXPrv r
instance Ord MockPrivateKey where
    compare (MockPrivateKey l) (MockPrivateKey r) = compare (Crypto.unXPrv l) (Crypto.unXPrv r)
instance Hashable MockPrivateKey where
    hashWithSalt i = hashWithSalt i . Crypto.unXPrv . unMockPrivateKey

-- | Emulated wallet with a key and a passphrase
data MockWallet =
    MockWallet
        { mwWalletId :: CW.WalletId
        , mwKey      :: MockPrivateKey
        }
        deriving Show

-- | Wrapper for config files and APIs
newtype WalletNumber = WalletNumber { getWallet :: Integer }
    deriving (Show, Eq, Ord, Generic)
    deriving newtype (ToHttpApiData, FromHttpApiData)
    deriving anyclass (FromJSON, ToJSON)

fromWalletNumber :: WalletNumber -> MockWallet
fromWalletNumber (WalletNumber i) = fromSeed (BSL.toStrict $ serialise i)

fromSeed :: BS.ByteString -> MockWallet
fromSeed bs = MockWallet{mwWalletId, mwKey} where
    missing = max 0 (32 - BS.length bs)
    bs' = bs <> BS.replicate missing 0
    mwWalletId = CW.WalletId
        $ fromMaybe (error "CardanoWallet: fromSeed: digestFromByteString")
        $ Crypto.digestFromByteString
        $ Crypto.hashWith Crypto.Blake2b_160
        $ getLedgerBytes
        $ getPubKey
        $ Crypto.toPublicKey k
    k = Crypto.generateFromSeed bs'
    mwKey = MockPrivateKey k

toWalletNumber :: MockWallet -> WalletNumber
toWalletNumber MockWallet{mwWalletId=w} = maybe (error "toWalletNumber: not a known wallet") (WalletNumber . toInteger . succ) $ findIndex ((==) w . mwWalletId) knownWallets

-- | The wallets used in mockchain simulations by default. There are
--   ten wallets by default.
knownWallets :: [MockWallet]
knownWallets = fromWalletNumber . WalletNumber <$> [1..10]

-- | Get a known wallet from an @Integer@ indexed from 1 to 10.
knownWallet :: Integer -> MockWallet
knownWallet = (knownWallets !!) . pred . fromInteger

-- | Mock wallet's private key
privateKey :: MockWallet -> PrivateKey
privateKey = unMockPrivateKey . mwKey

-- | The mock wallet's public key hash
pubKeyHash :: MockWallet -> PubKeyHash
pubKeyHash = Crypto.pubKeyHash . pubKey

-- | The mock wallet's public key
pubKey :: MockWallet -> PubKey
pubKey = Crypto.toPublicKey . unMockPrivateKey . mwKey
