{-# LANGUAGE PatternSynonyms #-}
module Cardano.Crypto.Wallet.Types
    ( ChainCode(..)
    , DerivationScheme(..)
    , DerivationIndex
    , pattern LatestScheme
    ) where

import           Control.DeepSeq (NFData)
import           Data.ByteArray  (ByteArrayAccess)
import           Data.ByteString (ByteString)
import           Data.Hashable   (Hashable)

import Foundation
import Foundation.Collection (nonEmpty_)
import Foundation.Check (Arbitrary(..), frequency)

type DerivationIndex = Word32

data DerivationScheme = DerivationScheme1 | DerivationScheme2
    deriving (Show, Eq, Ord, Enum, Bounded, Typeable)
instance Arbitrary DerivationScheme where
    arbitrary = frequency $ nonEmpty_ [ (1, pure DerivationScheme1), (1, pure DerivationScheme2) ]

pattern LatestScheme :: DerivationScheme
pattern LatestScheme = DerivationScheme2

newtype ChainCode = ChainCode ByteString
    deriving (Show, Eq, Ord, ByteArrayAccess, NFData, Hashable)
