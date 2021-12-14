{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings    #-}

module Crypto.Encoding.BIP39.Dictionary
    ( -- ** Dictionary
      Dictionary(..)
    , WordIndex
    , wordIndex
    , unWordIndex

    , DictionaryError(..)
    ) where

import           Basement.NormalForm
import           Basement.Compat.Typeable
import           Basement.Types.OffsetSize (Offset(..))
import           Basement.From (TryFrom(..))
import           Basement.Imports

-- | this discribe the property of the Dictionary and will alllow to
-- convert from a mnemonic phrase to 'MnemonicSentence'
--
-- This is especially needed to build the BIP39 'Seed'
--
data Dictionary = Dictionary
    { dictionaryIndexToWord :: WordIndex -> String
      -- ^ This function will retrieve the mnemonic word associated to the
      -- given 'WordIndex'.
    , dictionaryWordToIndex :: String -> Either DictionaryError WordIndex
      -- ^ This function will retrieve the 'WordIndex' from a given mnemonic
      -- word.
    , dictionaryTestWord :: String -> Bool
      -- ^ test a given word is in the dictionary
    , dictionaryWordSeparator :: String
      -- ^ joining string (e.g. space for english)
    }
  deriving (Typeable)

-- | Index of the mnemonic word in the 'Dictionary'
--
-- 'WordIndex' are within range of [0..2047]
--
newtype WordIndex = WordIndex { unWordIndex :: Offset String }
    deriving (Show, Eq, Ord, Typeable, NormalForm)
instance Enum WordIndex where
    toEnum = wordIndex . toEnum
    fromEnum = fromEnum . unWordIndex
    succ (WordIndex (Offset v))
        | v < 2047 = WordIndex (Offset (succ v))
        | otherwise = error "WordIndex out of bound"
    pred (WordIndex (Offset v))
        | v <= 0 = error "WordIndex out of bound"
        | otherwise = WordIndex (Offset (pred v))
instance Bounded WordIndex where
    minBound = WordIndex (Offset 0)
    maxBound = WordIndex (Offset 2047)
instance TryFrom (Offset String) WordIndex where
    tryFrom w
        | w < 2048  = Just (WordIndex w)
        | otherwise = Nothing
instance TryFrom Int WordIndex where
    tryFrom v
        | v >= 0    = tryFrom (Offset v :: Offset String)
        | otherwise = Nothing

wordIndex :: Offset String -> WordIndex
wordIndex w = case tryFrom w of
    Nothing -> error ("Error: word index should be between 0 to 2047. " <> show w)
    Just wi -> wi

-- -------------------------------------------------------------------------- --
-- Errors
-- -------------------------------------------------------------------------- --

data DictionaryError
    = ErrInvalidDictionaryWord String
    deriving (Show)

