{-# LANGUAGE GADTs                #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Crypto.Encoding.BIP39
    ( -- * Entropy
      Entropy
    , ValidEntropySize
    , Checksum
    , ValidChecksumSize
    , MnemonicWords
    , EntropySize
    , toEntropy
    , entropyRaw
    , entropyChecksum

    , entropyToWords
    , wordsToEntropy

    , -- * Seed
      Seed
    , Passphrase
    , sentenceToSeed
    , phraseToSeed

    , -- * Mnemonic Sentence
      MnemonicSentence
    , MnemonicPhrase
    , ValidMnemonicSentence
    , mnemonicPhrase
    , checkMnemonicPhrase
    , mnemonicPhraseToMnemonicSentence
    , mnemonicSentenceToMnemonicPhrase
    , mnemonicSentenceToString
    , mnemonicSentenceToListN
    , mnemonicPhraseToString
    , translateTo
    , -- ** Dictionary
      Dictionary(..)
    , WordIndex
    , wordIndex
    , unWordIndex

    , -- * helpers
      ConsistentEntropy
    , CheckSumBits
    , Elem

    , -- * Errors
      DictionaryError(..)
    , EntropyError(..)
    , MnemonicWordsError(..)
    ) where

import Prelude ((-), (*), (+), div, divMod, (^), fromIntegral)

import qualified Basement.String as String
import           Basement.Nat
import qualified Basement.Sized.List as ListN
import           Basement.Sized.List (ListN)
import           Basement.NormalForm
import           Basement.Compat.Typeable
import           Basement.Numerical.Number (IsIntegral(..))
import           Basement.Imports

import           Foundation.Check

import           Control.Monad (replicateM, (<=<))
import           Data.Bits
import           Data.Maybe (fromMaybe)
import           Data.List (reverse, intersperse, length)
import           Data.Kind (Constraint)
import           Data.ByteArray (ByteArrayAccess, ByteArray)
import qualified Data.ByteArray as BA
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS

import           Data.Proxy

import           GHC.TypeLits

import           Crypto.Hash (hashWith, SHA256(..))
import           Crypto.Number.Serialize (os2ip, i2ospOf_)
import qualified Crypto.KDF.PBKDF2 as PBKDF2

import           Crypto.Encoding.BIP39.Dictionary
import           Cardano.Internal.Compat (fromRight)

-- -------------------------------------------------------------------------- --
-- Entropy
-- -------------------------------------------------------------------------- --

-- | this is the `Checksum` of a given 'Entropy'
--
-- the 'Nat' type parameter represent the size, in bits, of this checksum.
newtype Checksum (bits :: Nat) = Checksum Word8
    deriving (Show, Eq, Typeable, NormalForm)

checksum :: forall csz ba . (KnownNat csz, ByteArrayAccess ba)
         => ba -> Checksum csz
checksum bs = Checksum $ (hashWith SHA256 bs `BA.index` 0) `shiftR` (8 - csz)
  where
    csz = fromInteger $ natVal (Proxy @csz)

type ValidChecksumSize (ent :: Nat) (csz :: Nat) =
    ( KnownNat csz, NatWithinBound Int csz
    , Elem csz '[3, 4, 5, 6, 7, 8]
    , CheckSumBits ent ~ csz
    )

-- | Number of bits of checksum related to a specific entropy size in bits
type family CheckSumBits (n :: Nat) :: Nat where
    CheckSumBits 96  = 3
    CheckSumBits 128 = 4
    CheckSumBits 160 = 5
    CheckSumBits 192 = 6
    CheckSumBits 224 = 7
    CheckSumBits 256 = 8

-- | BIP39's entropy is a byte array of a given size (in bits, see
-- 'ValidEntropySize' for the valid size).
--
-- To it is associated
data Entropy (n :: Nat) = Entropy
     { entropyRaw :: !ByteString
        -- ^ Get the raw binary associated with the entropy
     , entropyChecksum :: !(Checksum (CheckSumBits n))
        -- ^ Get the checksum of the Entropy
     }
  deriving (Show, Eq, Typeable)
instance NormalForm (Entropy n) where
    toNormalForm (Entropy !_ cs) = toNormalForm cs
instance Arbitrary (Entropy 96) where
    arbitrary = fromRight (error "arbitrary (Entropy 96)") . toEntropy . BS.pack <$> replicateM 12 arbitrary
instance Arbitrary (Entropy 128) where
    arbitrary = fromRight (error "arbitrary (Entropy 128)") . toEntropy . BS.pack <$> replicateM 16 arbitrary
instance Arbitrary (Entropy 160) where
    arbitrary = fromRight (error "arbitrary (Entropy 160)") . toEntropy . BS.pack <$> replicateM 20 arbitrary
instance Arbitrary (Entropy 192) where
    arbitrary = fromRight (error "arbitrary (Entropy 192)") . toEntropy . BS.pack <$> replicateM 24 arbitrary
instance Arbitrary (Entropy 224) where
    arbitrary = fromRight (error "arbitrary (Entropy 224)") . toEntropy . BS.pack <$> replicateM 28 arbitrary
instance Arbitrary (Entropy 256) where
    arbitrary = fromRight (error "arbitrary (Entropy 256)") . toEntropy . BS.pack <$> replicateM 32 arbitrary

-- | Type Constraint Alias to check a given 'Nat' is valid for an entropy size
--
-- i.e. it must be one of the following: 96, 128, 160, 192, 224, 256.
--
type ValidEntropySize (n :: Nat) =
    ( KnownNat n, NatWithinBound Int n
    , Elem n '[96, 128, 160, 192, 224, 256]
    )

-- | Create a specific entropy type of known size from a raw bytestring
toEntropy :: forall n csz ba
           . (ValidEntropySize n, ValidChecksumSize n csz, ByteArrayAccess ba)
          => ba
          -> Either (EntropyError csz) (Entropy n)
toEntropy bs
    | actual == expected = Right $ Entropy (BA.convert bs) (checksum @csz bs)
    | otherwise          = Left  $ ErrInvalidEntropyLength actual expected
  where
    actual   = BA.length bs*8
    expected = natValInt (Proxy @n)

toEntropyCheck :: forall n csz ba
                . (ValidEntropySize n, ValidChecksumSize n csz, ByteArrayAccess ba)
               => ba
               -> Checksum csz
               -> Either (EntropyError csz) (Entropy n)
toEntropyCheck bs s = case toEntropy bs of
    Left err -> Left err
    Right e@(Entropy _ cs) | cs == s   -> Right e
                           | otherwise -> Left $ ErrInvalidEntropyChecksum cs s

-- | Number of Words related to a specific entropy size in bits
type family MnemonicWords (n :: Nat) :: Nat where
    MnemonicWords 96  = 9
    MnemonicWords 128 = 12
    MnemonicWords 160 = 15
    MnemonicWords 192 = 18
    MnemonicWords 224 = 21
    MnemonicWords 256 = 24

-- | Corresponding entropy size in bits for a given number of words
type family EntropySize (n :: Nat) :: Nat where
    EntropySize 9  = 96
    EntropySize 12 = 128
    EntropySize 15 = 160
    EntropySize 18 = 192
    EntropySize 21 = 224
    EntropySize 24 = 256


-- | Type Constraint Alias to check the entropy size, the number of mnemonic
-- words and the checksum size is consistent. i.e. that the following is true:
--
-- |  entropysize  | checksumsize | entropysize + checksumsize | mnemonicsize |
-- +---------------+--------------+----------------------------+--------------+
-- |           96  |            3 |                        99  |           9  |
-- |          128  |            4 |                       132  |          12  |
-- |          160  |            5 |                       165  |          15  |
-- |          192  |            6 |                       198  |          18  |
-- |          224  |            7 |                       231  |          21  |
-- |          256  |            8 |                       264  |          24  |
--
-- This type constraint alias also perform all the GHC's cumbersome type level
-- literal handling.
--
type ConsistentEntropy ent mw csz =
    ( ValidEntropySize ent
    , ValidChecksumSize ent csz
    , ValidMnemonicSentence mw
    , MnemonicWords ent ~ mw
    )

-- | retrieve the initial entropy from a given 'MnemonicSentence'
--
-- This function validate the retrieved 'Entropy' is valid, i.e. that the
-- checksum is correct.
-- This means you should not create a new 'Entropy' from a 'MnemonicSentence',
-- instead, you should use a Random Number Generator to create a new 'Entropy'.
--
wordsToEntropy :: forall ent csz mw
                . ConsistentEntropy ent mw csz
               => MnemonicSentence mw
               -> Either (EntropyError csz) (Entropy ent)
wordsToEntropy (MnemonicSentence ms) =
    let -- we don't revese the list here, we know that the first word index
        -- is the highest first 11 bits of the entropy.
        entropy         = ListN.foldl' (\acc x -> acc `shiftL` 11 + toInteger (unWordIndex x)) 0 ms
        initialEntropy :: ByteString
        initialEntropy = i2ospOf_ nb (entropy `shiftR` fromInteger checksumsize)
        cs = Checksum $ fromInteger (entropy .&. mask)
     in toEntropyCheck initialEntropy cs
  where
    checksumsize = natVal (Proxy @csz)
    entropysize  = natVal (Proxy @ent)
    nb  = fromInteger entropysize `div` 8
    mask = 2 ^ checksumsize - 1

-- | Given an entropy of size n, Create a list
--
entropyToWords :: forall n csz mw . ConsistentEntropy n mw csz
               => Entropy n
               -> MnemonicSentence mw
entropyToWords (Entropy bs (Checksum w)) =
    fromList $ reverse $ loop mw g
  where
    g = (os2ip bs `shiftL` fromIntegral csz) .|. fromIntegral w
    csz = natVal (Proxy @csz)
    mw  = natVal (Proxy @mw)
    loop nbWords acc
        | nbWords == 0 = []
        | otherwise    =
            let (acc', d) = acc `divMod` 2048
             in wordIndex (fromIntegral d) : loop (nbWords - 1) acc'

-- -------------------------------------------------------------------------- --
-- Seed
-- -------------------------------------------------------------------------- --

newtype Seed = Seed ByteString
  deriving (Show, Eq, Ord, Typeable, Semigroup, Monoid, ByteArrayAccess, ByteArray, IsString)

type Passphrase = String

-- | Create a seed from 'MmemonicSentence' and 'Passphrase' using the BIP39
-- algorithm.
sentenceToSeed :: ValidMnemonicSentence mw
               => MnemonicSentence mw -- ^ 'MmenomicPhrase' of mw words
               -> Dictionary          -- ^  Dictionary' of words/indexes
               -> Passphrase          -- ^ 'Passphrase' used to generate
               -> Seed
sentenceToSeed mw dic =
    phraseToSeed (mnemonicSentenceToMnemonicPhrase dic mw) dic

-- | Create a seed from 'MmemonicPhrase' and 'Passphrase' using the BIP39
-- algorithm.
phraseToSeed :: ValidMnemonicSentence mw
             => MnemonicPhrase mw -- ^ 'MmenomicPhrase' of mw words
             -> Dictionary        -- ^  Dictionary' of words/indexes
             -> Passphrase        -- ^ 'Passphrase' used to generate
             -> Seed
phraseToSeed mw dic passphrase =
    PBKDF2.fastPBKDF2_SHA512
                    (PBKDF2.Parameters 2048 64)
                    sentence
                    (toData ("mnemonic" `mappend` passphrase))
  where
    sentence = toData $ mnemonicPhraseToString dic mw
    toData = String.toBytes String.UTF8


-- -------------------------------------------------------------------------- --
-- Mnemonic Sentence and Mnemonic Phrase
-- -------------------------------------------------------------------------- --

-- | Mnemonic Sentence is a list of 'WordIndex'.
--
-- This is the generic representation of a mnemonic phrase that can be used for
-- transalating to a different dictionary (example: English to Japanese).
--
-- This is mainly used to convert from/to the 'Entropy' and for 'cardanoSlSeed'
--
newtype MnemonicSentence (mw :: Nat) = MnemonicSentence
    { mnemonicSentenceToListN :: ListN mw WordIndex
    }
  deriving (Show, Eq, Ord, Typeable, NormalForm)
instance ValidMnemonicSentence mw => IsList (MnemonicSentence mw) where
    type Item (MnemonicSentence mw) = WordIndex
    fromList = MnemonicSentence . fromMaybe (error "invalid mnemonic size") . ListN.toListN
    toList = ListN.unListN . mnemonicSentenceToListN

-- | Type Constraint to validate the given 'Nat' is valid for the supported
-- 'MnemonicSentence'
type ValidMnemonicSentence (mw :: Nat) =
    ( KnownNat mw
    , NatWithinBound Int mw
    , Elem mw '[9, 12, 15, 18, 21, 24]
    )

-- | Human readable representation of a 'MnemonicSentence'
--
newtype MnemonicPhrase (mw :: Nat) = MnemonicPhrase
    { mnemonicPhraseToListN :: ListN mw String
    }
  deriving (Show, Eq, Ord, Typeable, NormalForm)
instance ValidMnemonicSentence mw => IsList (MnemonicPhrase mw) where
    type Item (MnemonicPhrase mw) = String
    fromList = fromRight (error "invalid mnemonic phrase") . mnemonicPhrase
    toList = ListN.unListN . mnemonicPhraseToListN

mnemonicPhrase :: forall mw . ValidMnemonicSentence mw => [String] -> Either MnemonicWordsError (MnemonicPhrase mw)
mnemonicPhrase l = MnemonicPhrase <$> maybe
    (Left $ ErrWrongNumberOfWords (length l) (natValInt @mw Proxy))
     Right
    (ListN.toListN l)
{-# INLINABLE mnemonicPhrase #-}

-- | check a given 'MnemonicPhrase' is valid for the given 'Dictionary'
--
checkMnemonicPhrase :: forall mw . ValidMnemonicSentence mw
                    => Dictionary
                    -> MnemonicPhrase mw
                    -> Bool
checkMnemonicPhrase dic (MnemonicPhrase ln) =
    ListN.foldl' (\acc s -> (dictionaryTestWord dic s && acc)) True ln

-- | convert the given 'MnemonicPhrase' to a generic 'MnemonicSentence'
-- with the given 'Dictionary'.
--
-- This function assumes the 'Dictionary' and the 'MnemonicPhrase' are
-- compatible (see 'checkMnemonicPhrase').
--
mnemonicPhraseToMnemonicSentence :: forall mw . ValidMnemonicSentence mw
                                 => Dictionary
                                 -> MnemonicPhrase mw
                                 -> Either DictionaryError (MnemonicSentence mw)
mnemonicPhraseToMnemonicSentence dic (MnemonicPhrase ln) = MnemonicSentence <$>
    ListN.mapM (dictionaryWordToIndex dic) ln

-- | convert the given generic 'MnemonicSentence' to a human readable
-- 'MnemonicPhrase' targetting the language of the given 'Dictionary'.
mnemonicSentenceToMnemonicPhrase :: forall mw . ValidMnemonicSentence mw
                                 => Dictionary
                                 -> MnemonicSentence mw
                                 -> MnemonicPhrase mw
mnemonicSentenceToMnemonicPhrase dic (MnemonicSentence ln) = MnemonicPhrase $
    ListN.map (dictionaryIndexToWord dic) ln

mnemonicPhraseToString :: forall mw . ValidMnemonicSentence mw
                       => Dictionary
                       -> MnemonicPhrase mw
                       -> String
mnemonicPhraseToString dic (MnemonicPhrase ln) = mconcat $
    intersperse (dictionaryWordSeparator dic) (ListN.unListN ln)

mnemonicSentenceToString :: forall mw . ValidMnemonicSentence mw
                         => Dictionary
                         -> MnemonicSentence mw
                         -> String
mnemonicSentenceToString dic = mnemonicPhraseToString dic
                             . mnemonicSentenceToMnemonicPhrase dic

-- | translate the given 'MnemonicPhrase' from one dictionary into another.
--
-- This function assumes the source dictionary is compatible with the given
-- 'MnemonicPhrase' (see 'checkMnemonicPhrase')
--
translateTo :: forall mw . ValidMnemonicSentence mw
            => Dictionary -- ^ source dictionary
            -> Dictionary -- ^ destination dictionary
            -> MnemonicPhrase mw
            -> Either DictionaryError (MnemonicPhrase mw)
translateTo dicSrc dicDst (MnemonicPhrase ln) = MnemonicPhrase <$>
    ListN.mapM (return . dictionaryIndexToWord dicDst <=< dictionaryWordToIndex dicSrc) ln

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

-- | convenient type level constraint to validate a given 'Nat' e is an elemnt
-- of the list of 'Nat' l.
type family Elem (e :: Nat) (l :: [Nat]) :: Constraint where
    Elem e '[] = TypeError ('Text "offset: field "
             ':<>: 'ShowType e
             ':<>: 'Text " not elements of valids values")
    Elem e (e ': _) = ()
    Elem e (_ ': xs) = Elem e xs

-- -------------------------------------------------------------------------- --
-- Errors
-- -------------------------------------------------------------------------- --

data EntropyError csz
    = ErrInvalidEntropyLength
          Int             --  Actual length in bits
          Int             --  Expected length in bits
    | ErrInvalidEntropyChecksum
          (Checksum csz)  --  Actual checksum
          (Checksum csz)  --  Expected checksum
    deriving (Show)

data MnemonicWordsError
    = ErrWrongNumberOfWords
          Int -- Actual number of words
          Int -- Expected number of words
    deriving (Show)
