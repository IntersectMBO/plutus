{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}

module Wallet.Emulator.MockWallet(
    MockWallet(..),
    fromWalletNumber
    ) where

import           Cardano.Address.Derivation                         (XPrv)
import           Cardano.Mnemonic                                   (ConsistentEntropy, Entropy, EntropySize, Mnemonic,
                                                                     MnemonicWords, SomeMnemonic (..),
                                                                     ValidChecksumSize, ValidEntropySize,
                                                                     ValidMnemonicSentence, entropyToMnemonic,
                                                                     mkEntropy, mkMnemonic)
import           Cardano.Wallet.Primitive.AddressDerivation         (Depth (RootK), Passphrase (..),
                                                                     PassphraseScheme (EncryptWithPBKDF2), digest,
                                                                     preparePassphrase, publicKey)
import           Cardano.Wallet.Primitive.AddressDerivation.Shelley (ShelleyKey, generateKeyFromSeed)
import qualified Cardano.Wallet.Primitive.Types                     as CW
import           Cardano.Wallet.Unsafe                              (unsafeMkSomeMnemonicFromEntropy)
import qualified Data.ByteArray                                     as BA
import qualified Data.ByteString                                    as BS
import           Data.Proxy                                         (Proxy (..))
import           GHC.Stack                                          (HasCallStack)
import           GHC.TypeLits                                       (natVal)
import           Wallet.Emulator                                    (WalletNumber (..))
import qualified Wallet.Emulator.Wallet                             as EM

-- | Emulated wallet with a key and a passphrase
data MockWallet =
    MockWallet
        { mwWallet     :: EM.Wallet
        , mwKey        :: ShelleyKey 'RootK XPrv
        , mwPassPhrase :: Passphrase "encryption"
        }
        deriving (Eq, Show)

fromWalletNumber :: WalletNumber -> MockWallet
fromWalletNumber (WalletNumber i) = MockWallet{mwWallet, mwKey, mwPassPhrase} where
    mwWallet = EM.Wallet $ EM.WalletId $ CW.WalletId $ digest $ publicKey mwKey
    mwKey = generateKeyFromSeed (mockWalletMnemonic i, Nothing) mwPassPhrase
    bytes :: BS.ByteString = "123456789password"
    mwPassPhrase = preparePassphrase EncryptWithPBKDF2 $ Passphrase $ BA.convert bytes

-- |
mockWalletMnemonic
    :: forall ent csz.
        ( HasCallStack
        , ValidEntropySize ent
        , ValidChecksumSize ent csz
        , ValidMnemonicSentence 15
        , ent ~ EntropySize 15
        , 15 ~ MnemonicWords ent
        )
    => Integer
    -> SomeMnemonic
mockWalletMnemonic i =
    let
        proxy = Proxy @15
        n = fromIntegral $ natVal (Proxy @ent) `div` 8
        entropy = BS.replicate n (fromInteger i)
    in
        unsafeMkSomeMnemonicFromEntropy proxy entropy
