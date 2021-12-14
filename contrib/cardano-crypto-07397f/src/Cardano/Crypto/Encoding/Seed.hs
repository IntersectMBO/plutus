-- |
-- Module      : Cardano.Crypto.Encoding.Seed
-- Description : tools relating to Paper Wallet
-- Maintainer  : nicolas.diprima@iohk.io
--
-- implementation of the proposal specification for Paper Wallet
-- see https://github.com/input-output-hk/cardano-specs/blob/master/proposals/0001-PaperWallet.md
--
-- however we allow more genericity in the implementation to allow
-- not only 12 mnemonic words to freeze but also 15, 18 and 21.
--
-- because the output mnemonic words are always 3 words longer (for the IV)
-- we cannot use 24 words long mnemonic sentence.
--
-- assumption:
--
-- * we use 'PBKDF2' with 'HMAC 512' to generate the OTP.
-- * we use 10000 iteration for the PBKDF2
-- * we use the 4 bytes "IOHK" for the CONSTANT
--

{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}

module Cardano.Crypto.Encoding.Seed
    ( Entropy
    , Passphrase
    , MnemonicSentence
    , ConsistentEntropy
    , ScrambleIV
    , mkScrambleIV
    , scramble
    , unscramble

    , IVSizeWords
    , IVSizeBits

    , -- helpers
      scrambleMnemonic
    ) where

import Foundation
import Foundation.Check
import Basement.Nat
import Crypto.Error

import Data.ByteArray (xor, ScrubbedBytes)
import Crypto.Encoding.BIP39
import qualified Crypto.KDF.PBKDF2 as PBKDF2
import           Basement.Sized.List (ListN)
import qualified Basement.Sized.List as ListN
import Data.ByteArray (ByteArrayAccess)

import Data.ByteString (ByteString)
import qualified Data.ByteString as B

type IVSizeWords = 6
type IVSizeBytes = 8
type IVSizeBits  = 64

ivSizeBytes :: Int
ivSizeBytes = 8

-- | Number of iteration of the PBKDF2
iterations :: Int
iterations = 10000

newtype ScrambleIV = ScrambleIV ByteString
    deriving (Eq,Ord,Show,Typeable,ByteArrayAccess)
instance Arbitrary ScrambleIV where
    arbitrary = do
        l <- arbitrary :: Gen (ListN IVSizeBytes Word8)
        pure $ throwCryptoError $ mkScrambleIV $ B.pack $ ListN.unListN l

mkScrambleIV :: ByteString -> CryptoFailable ScrambleIV
mkScrambleIV bs
    | B.length bs == ivSizeBytes = CryptoPassed (ScrambleIV bs)
    | otherwise                  = CryptoFailed CryptoError_IvSizeInvalid

-- | scramble the given entropy into an entropy slighly larger.
--
-- This entropy can then be converted to a mnemonic sentence:
--
-- @
-- freeze iv mnemonics passphrase = entropyToWords . scramble iv entropy passphrase
--   where
--     entropy = case wordsToEntropy mnemonics of
--         Nothing -> error "mnemonic to entropy failed"
--         Just e  -> e
-- @
scramble :: forall entropysizeI entropysizeO mnemonicsize scramblesize csI csO
         . ( ConsistentEntropy entropysizeI mnemonicsize csI
           , ConsistentEntropy entropysizeO scramblesize csO
           , (mnemonicsize + IVSizeWords) ~ scramblesize
           , (entropysizeI + IVSizeBits)  ~ entropysizeO
           )
         => ScrambleIV
         -> Entropy entropysizeI
         -> Passphrase
         -> Entropy entropysizeO
scramble (ScrambleIV iv) e passphrase =
    let salt = iv
        otp :: ScrubbedBytes
        otp = PBKDF2.fastPBKDF2_SHA512
                    (PBKDF2.Parameters iterations entropySize)
                    passphrase
                    salt
        ee = xor otp (entropyRaw e)
     in case toEntropy @entropysizeO (iv <> ee) of
            Left err -> error $ "scramble: the function BIP39.toEntropy returned an error: " <> show err
            Right e' -> e'
  where
    entropySize = fromIntegral (natVal (Proxy @entropysizeI)) `div` 8

-- | helper function to scramble mnemonics
scrambleMnemonic :: forall entropysizeI entropysizeO mnemonicsize scramblesize csI csO
                 . ( ConsistentEntropy entropysizeI mnemonicsize csI
                   , ConsistentEntropy entropysizeO scramblesize csO
                   , (mnemonicsize + IVSizeWords) ~ scramblesize
                   , (entropysizeI + IVSizeBits)  ~ entropysizeO
                   )
                 => Proxy entropysizeI
                 -> ScrambleIV
                 -> MnemonicSentence mnemonicsize
                 -> Passphrase
                 -> MnemonicSentence scramblesize
scrambleMnemonic _ iv mw passphrase =
      entropyToWords @entropysizeO
    $ scramble @entropysizeI @entropysizeO iv entropy passphrase
  where
    entropy = case wordsToEntropy @entropysizeI mw of
        Left  err -> error $ "mnemonic to entropy failed: " <> show err
        Right e   -> e

-- |
-- The reverse operation of 'scramble'
--
-- This function recovers the original entropy from the given scrambled entropy
-- and the associated password.
--
-- @
-- recover scrambled passphrase = entropyToWords @entropysizeO .
--     unscramble @entropysizeI @entropysizeO entropyScrambled passphrase
--   where
--     entropyScrambled = case wordsToEntropy @entropysizeI scrambled of
--         Nothing -> error "mnemonic to entropy failed"
--         Just e  -> e
-- @
--
unscramble :: forall entropysizeI entropysizeO mnemonicsize scramblesize csI csO
           . ( ConsistentEntropy entropysizeI scramblesize csI
             , ConsistentEntropy entropysizeO mnemonicsize csO
             , (mnemonicsize + IVSizeWords) ~ scramblesize
             , (entropysizeO + IVSizeBits)  ~ entropysizeI
             )
          => Entropy entropysizeI
          -> Passphrase
          -> Entropy entropysizeO
unscramble e passphrase =
    let ee = xor otp eraw :: ByteString
     in case toEntropy @entropysizeO ee of
      Left err -> error $ "unscramble: the function BIP39.toEntropy returned an error: " <> show err
      Right e' -> e'
  where
    (iv, eraw) = B.splitAt ivSizeBytes (entropyRaw e) :: (ByteString, ByteString)
    salt = iv
    otp :: ScrubbedBytes
    otp = PBKDF2.fastPBKDF2_SHA512
                  (PBKDF2.Parameters iterations entropySize)
                  passphrase
                  salt
    entropySize = fromIntegral (natVal (Proxy @entropysizeO)) `div` 8
