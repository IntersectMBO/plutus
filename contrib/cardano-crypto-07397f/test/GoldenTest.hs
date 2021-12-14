{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Basement.Nat
import qualified Basement.Sized.List as LN

import Foundation
import Foundation.Check
import qualified Foundation.Parser as Parser
import Foundation.Collection ((!), nonEmpty_)
import Foundation.String
import Foundation.String.Read (readIntegral)

import Data.List (elemIndex)
import Control.Arrow (left)

import Inspector
import qualified Inspector.TestVector.Types as Type
import qualified Inspector.TestVector.Value as Value

import Data.ByteArray (Bytes, convert)
import qualified Data.ByteArray as B

import           Cardano.Crypto.Wallet
import           Cardano.Crypto.Encoding.Seed
import           Cardano.Crypto.Encoding.BIP39
import           Crypto.Encoding.BIP39.English (english)
import           Cardano.Internal.Compat (fromRight)

import Test.Orphans

main :: IO ()
main = defaultTest $ do
    goldenSignatureEd25519
    goldenBIP39
    goldenHDWallet
    goldenPaperwallet

-- -------------------------------------------------------------------------- --

type GoldenPaperWallet n
    = "cardano" :> "crypto" :> PathParameter "scramble" n
      :> Payload "iv"     ScrambleIV
      :> Payload "input" (Mnemonic 'English (MnemonicWords n))
      :> Payload "passphrase" Passphrase
      :> Payload "shielded_input" (Mnemonic 'English (MnemonicWords (n + IVSizeBits)))

goldenPaperwallet :: GoldenT ()
goldenPaperwallet = group $ do
    golden (Proxy :: Proxy (GoldenPaperWallet 128)) $ \iv (Mnemonic input) pw ->
        Mnemonic (scrambleMnemonic (Proxy @128) iv input pw)
    golden (Proxy :: Proxy (GoldenPaperWallet 160)) $ \iv (Mnemonic input) pw ->
        Mnemonic (scrambleMnemonic (Proxy @160) iv input pw)
    golden (Proxy :: Proxy (GoldenPaperWallet 192)) $ \iv (Mnemonic input) pw ->
        Mnemonic (scrambleMnemonic (Proxy @192) iv input pw)

-- -------------------------------------------------------------------------- --

type HDWallet n
    = "cardano" :> "crypto" :> "wallet" :> PathParameter "BIP39-" n
      :> Payload "words" (Mnemonic 'English (MnemonicWords n))
      :> Payload "passphrase" Passphrase
      :> Payload "master_key_generation" MasterKeyGeneration
      :> Payload "derivation_scheme" DerivationScheme
      :> Payload "path" ChainCodePath
      :> Payload "data_to_sign" String
      :> ( Payload "xPub" XPub
         , Payload "xPriv" XPrv
         , Payload "signature" XSignature
         , Payload "seed" Seed
         )

goldenHDWallet :: GoldenT ()
goldenHDWallet = group $ do
    summary "This test vectors uses the `Cardano.Crypto.Wallet` primitives to produce extended\n\
            \private keys which are _encrypted_ with a passphrase. A passphrase can be empty as well.\n\
            \Under this schema, we support only hardened key derivation."

    golden (Proxy :: Proxy (HDWallet 128)) (runTest (Proxy @128))
    golden (Proxy :: Proxy (HDWallet 160)) (runTest (Proxy @160))
    golden (Proxy :: Proxy (HDWallet 192)) (runTest (Proxy @192))
    golden (Proxy :: Proxy (HDWallet 224)) (runTest (Proxy @224))
    golden (Proxy :: Proxy (HDWallet 256)) (runTest (Proxy @256))
  where
    runTest :: forall n csz mw . ConsistentEntropy n mw csz
            => Proxy n
            -> Mnemonic 'English mw
            -> Passphrase
            -> MasterKeyGeneration
            -> DerivationScheme
            -> ChainCodePath
            -> String
            -> (XPub, XPrv, XSignature, Seed)
    runTest p (Mnemonic mw) pw mkg ds (Root path) toSign =
        let -- 1. retrieve the seed
            -- 1. retrieve the seed and 2. generate from the seed
            (seed, master) = case mkg of
                        MasterKeyRetryOld ->
                            let seedX = fromMaybe (error "Invalid Mnemonic, cannot retrieve the `Seed'")
                                                 (cardanoSlSeed p mw)
                             in (seedX, generate seedX pw)
                        MasterKeyPBKDF    ->
                            let seedX = seedFromMnemonics p mw
                             in (seedX, generateNew seedX (B.empty :: Bytes) pw)
            -- 3. get the XPrv from the master and the path
            priv = deriveWith master path
            -- 4. get the public key
            pub = toXPub priv
            -- 5. sign some data
            s = sign pw priv toSign
         in (pub, priv, s, seed)
      where
        deriveWith :: XPrv -> [Word32] -> XPrv
        deriveWith = foldl' (deriveXPrv ds pw)

        seedFromMnemonics :: forall n csz mw . ConsistentEntropy n mw csz
                          => Proxy n
                          -> MnemonicSentence mw
                          -> Seed
        seedFromMnemonics _ mw =
            case wordsToEntropy @n @csz @mw mw of
                Left _ -> error "Invalid Mnemonic"
                Right e -> B.convert $ entropyRaw e

-- -------------------------------------------------------------------------- --

type BIP39 n
    = "crypto" :> "encoding" :> PathParameter "BIP39-" n
      :> Payload "words" (Mnemonic 'English (MnemonicWords n))
      :> Payload "passphrase" Passphrase
      :> ( Payload "entropy" (Entropy n)
         , Payload "seed" Seed
         )

goldenBIP39 :: GoldenT ()
goldenBIP39 = group $ do
    summary "Test official BIP39"

    golden (Proxy :: Proxy (BIP39 128)) (runTest (Proxy @128))
    -- golden (Proxy :: Proxy (BIP39 160)) (runTest (Proxy @160))
    golden (Proxy :: Proxy (BIP39 192)) (runTest (Proxy @192))
    -- golden (Proxy :: Proxy (BIP39 224)) (runTest (Proxy @224))
    golden (Proxy :: Proxy (BIP39 256)) (runTest (Proxy @256))
  where
    runTest :: forall n csz mw . ConsistentEntropy n mw csz
            => Proxy n
            -> Mnemonic 'English mw
            -> Passphrase
            -> (Entropy n, Seed)
    runTest p (Mnemonic mw) pw  =
        let -- 1. retrieve the entroy
            entropy = fromRight (error "invalid mnemonic phrase")
                                (wordsToEntropy @n mw)
            -- 2. retrieve the seed
            seed = sentenceToSeed @mw mw english pw
         in (entropy, seed)

-- -------------------------------------------------------------------------- --

type SignatureEd25519
    = "cardano" :> "crypto" :> "signature-ed25519"
      :> Payload "xpub" XPub
      :> Payload "data" Bytes
      :> Payload "signature" XSignature
      :> Payload "valid" Bool

goldenSignatureEd25519 :: GoldenT ()
goldenSignatureEd25519 = golden (Proxy :: Proxy SignatureEd25519) verify

-- -------------------------------------------------------------------------- --
--                          Helpers                                           --
-- -------------------------------------------------------------------------- --

-- | `m/0'/1'/1000'`
newtype ChainCodePath = Root [Word32]
  deriving (Show, Eq, Typeable)
instance Arbitrary ChainCodePath where
    arbitrary = Root <$> arbitrary

instance Inspectable ChainCodePath where
    documentation _ = "Derivation Chain code path: list of derivation path."
    exportType    _ = Type.Array $ Type.UnsizedArray Type.Unsigned32
    builder (Root l) = builder l
    parser        v = Root <$> parser v

-- Enum for the support language to read/write from mnemonic
data Language = English

-- | a convenient type to help read/parse/document expected input of type
-- BIP39 mnemonics
newtype Mnemonic (k :: Language) n = Mnemonic (MnemonicSentence n)
  deriving (Eq, Typeable)

-- | The type of master key generation
data MasterKeyGeneration = MasterKeyRetryOld | MasterKeyPBKDF
    deriving (Show,Eq)

instance Inspectable MasterKeyGeneration where
    documentation _ = "Master Key Derivation: list of derivation path."
    exportType    _ = Type.String
    builder MasterKeyRetryOld = Value.String "retry-old"
    builder MasterKeyPBKDF = Value.String "pbkdf"
    parser          = withString "MasterKeyGeneration" $ \str -> case str of
        "retry-old" -> pure MasterKeyRetryOld
        "pbkdf"     -> pure MasterKeyPBKDF
        _           -> Left $ "Expected either `retry-old' or `pbkdf' but found: `" <> str <> "'"

instance Arbitrary MasterKeyGeneration where
    arbitrary = elements $ nonEmpty_ [MasterKeyRetryOld, MasterKeyPBKDF]

instance Arbitrary (Mnemonic 'English 12) where
    arbitrary = Mnemonic . entropyToWords @128 @4 @12 <$> arbitrary
instance Arbitrary (Mnemonic 'English 15) where
    arbitrary = Mnemonic . entropyToWords @160 @5 @15 <$> arbitrary
instance Arbitrary (Mnemonic 'English 18) where
    arbitrary = Mnemonic . entropyToWords @192 @6 @18 <$> arbitrary
instance Arbitrary (Mnemonic 'English 21) where
    arbitrary = Mnemonic . entropyToWords @224 @7 @21 <$> arbitrary
instance Arbitrary (Mnemonic 'English 24) where
    arbitrary = Mnemonic . entropyToWords @256 @8 @24 <$> arbitrary

instance ValidMnemonicSentence n => Inspectable (Mnemonic 'English n) where
    documentation _ = "BIP39 mnemonic sentence (in English) of " <> show n <> " BIP39 Enlighs words"
      where
        n = natVal @n Proxy
    exportType    _ = Type.String
    builder (Mnemonic l) = Value.String $ mnemonicSentenceToString english l
    parser v = do
        strs <- words <$> parser v
        phrase <- left show $ mnemonicPhrase @n strs
        left show $ Mnemonic <$> mnemonicPhraseToMnemonicSentence english phrase
      where
        n = natVal @n Proxy

instance Arbitrary XSignature where
    arbitrary = undefined
instance Arbitrary Bytes where
    arbitrary = undefined
instance Arbitrary XPub where
    arbitrary = undefined
