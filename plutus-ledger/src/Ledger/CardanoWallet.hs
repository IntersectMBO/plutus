{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}

{- Cardano wallet implementation for the emulator. Uses 'cardano-wallet' for all
crypto.
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

import           Cardano.Address.Derivation                         (XPrv)
import qualified Cardano.Crypto.Wallet                              as Crypto
import           Cardano.Mnemonic                                   (EntropySize, MnemonicWords, SomeMnemonic (..),
                                                                     ValidChecksumSize, ValidEntropySize)
import           Cardano.Wallet.Primitive.AddressDerivation         (Depth (RootK), Passphrase (..),
                                                                     PassphraseScheme (EncryptWithPBKDF2), digest,
                                                                     preparePassphrase, publicKey)
import           Cardano.Wallet.Primitive.AddressDerivation.Shelley (ShelleyKey (..), generateKeyFromSeed)
import qualified Cardano.Wallet.Primitive.Types                     as CW
import           Cardano.Wallet.Unsafe                              (unsafeMkSomeMnemonicFromEntropy)
import           Codec.Serialise                                    (serialise)
import           Data.Aeson                                         (FromJSON, ToJSON)
import           Data.Aeson.Extras                                  (encodeByteString)
import qualified Data.ByteArray                                     as BA
import qualified Data.ByteString                                    as BS
import qualified Data.ByteString.Lazy                               as BSL
import           Data.Hashable                                      (Hashable (..))
import           Data.List                                          (findIndex)
import           Data.Proxy                                         (Proxy (..))
import qualified Data.Text                                          as T
import           GHC.Generics                                       (Generic)
import           GHC.Stack                                          (HasCallStack)
import           GHC.TypeLits                                       (natVal)
import           Ledger.Crypto                                      (PrivateKey, PubKey (..), PubKeyHash (..))
import qualified Ledger.Crypto                                      as Crypto
import qualified PlutusTx.Prelude                                   as PlutusTx
import           Servant.API                                        (FromHttpApiData (..), ToHttpApiData (..))

newtype MockPrivateKey = MockPrivateKey { unMockPrivateKey :: ShelleyKey 'RootK XPrv }

instance Show MockPrivateKey where
    show = T.unpack . encodeByteString . Crypto.unXPrv . getKey . unMockPrivateKey
instance Eq MockPrivateKey where
    (MockPrivateKey (ShelleyKey l)) == (MockPrivateKey (ShelleyKey r)) = Crypto.unXPrv l == Crypto.unXPrv r
instance Ord MockPrivateKey where
    compare (MockPrivateKey (ShelleyKey l)) (MockPrivateKey (ShelleyKey r)) = compare (Crypto.unXPrv l) (Crypto.unXPrv r)
instance Hashable MockPrivateKey where
    hashWithSalt i = hashWithSalt i . Crypto.unXPrv . getKey . unMockPrivateKey

-- | Emulated wallet with a key and a passphrase
data MockWallet =
    MockWallet
        { mwWalletId   :: CW.WalletId
        , mwKey        :: MockPrivateKey
        , mwPassPhrase :: Passphrase "encryption"
        }
        deriving Show

-- | Wrapper for config files and APIs
newtype WalletNumber = WalletNumber { getWallet :: Integer }
    deriving (Show, Eq, Ord, Generic)
    deriving newtype (ToHttpApiData, FromHttpApiData)
    deriving anyclass (FromJSON, ToJSON)

fromWalletNumber :: WalletNumber -> MockWallet
fromWalletNumber (WalletNumber i) = MockWallet{mwWalletId, mwKey, mwPassPhrase} where
    mwWalletId = CW.WalletId $ digest $ publicKey k
    k = generateKeyFromSeed (mockWalletMnemonic i, Nothing) mwPassPhrase
    mwKey = MockPrivateKey k
    bytes :: BS.ByteString = "123456789password"
    mwPassPhrase = preparePassphrase EncryptWithPBKDF2 $ Passphrase $ BA.convert bytes

fromSeed :: BS.ByteString -> MockWallet
fromSeed bs = MockWallet{mwWalletId, mwKey, mwPassPhrase} where
    mwWalletId = CW.WalletId $ digest $ publicKey k
    k = generateKeyFromSeed (seedMnemonic bs, Nothing) mwPassPhrase
    mwKey = MockPrivateKey k
    bytes :: BS.ByteString = "123456789password"
    mwPassPhrase = preparePassphrase EncryptWithPBKDF2 $ Passphrase $ BA.convert bytes

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
privateKey = getKey . unMockPrivateKey . mwKey

-- | The mock wallet's public key hash
pubKeyHash :: MockWallet -> PubKeyHash
pubKeyHash MockWallet{mwWalletId=CW.WalletId i} = PubKeyHash . PlutusTx.toBuiltin @BS.ByteString $ BA.convert i

-- | The mock wallet's public key
pubKey :: MockWallet -> PubKey
pubKey = Crypto.toPublicKey . getKey . unMockPrivateKey . mwKey

seedMnemonic ::
    forall ent csz.
    ( HasCallStack
    , ValidEntropySize ent
    , ValidChecksumSize ent csz
    , ent ~ EntropySize 15
    , 15 ~ MnemonicWords ent
    )
    => BS.ByteString
    -> SomeMnemonic
seedMnemonic bs =
    let
        proxy = Proxy @15
        n = fromIntegral $ natVal (Proxy @ent) `div` 8
        missing = max 0 (n - BS.length bs)
        entropy = BS.take n (BS.replicate missing 0 <> bs) -- pad with 0s to get the required length
    in
        unsafeMkSomeMnemonicFromEntropy proxy entropy


-- | Enumerate mnemonics
mockWalletMnemonic ::
    forall ent csz.
    ( HasCallStack
    , ValidEntropySize ent
    , ValidChecksumSize ent csz
    , ent ~ EntropySize 15
    , 15 ~ MnemonicWords ent
    )
    => Integer
    -> SomeMnemonic
mockWalletMnemonic = seedMnemonic . BSL.toStrict . serialise

-- test :: Bool
-- test = Crypto.verify pk msg sig where
--     msg = "Hello, world"
--     sig =
