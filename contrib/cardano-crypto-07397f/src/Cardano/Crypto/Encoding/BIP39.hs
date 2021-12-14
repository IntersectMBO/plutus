{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Cardano.Crypto.Encoding.BIP39
    ( cardanoSlSeed
    , module X
    ) where

import           Data.Proxy (Proxy)
import           Data.ByteString (ByteString)
import qualified Data.ByteArray as BA
import           Crypto.Hash (Blake2b_256, Digest, hash)

import           Crypto.Encoding.BIP39 as X

-- | **this is not a BIP39 function**
--
-- This function is the function used in `cardano-sl` (and Daedalus) to
-- generate a seed from a given mnemonic list.
--
-- https://github.com/input-output-hk/cardano-sl/blob/f5b8073b92b8219ae5fbb038c0ceb4a19502a86b/wallet/src/Pos/Util/BackupPhrase.hs#L59-L65
-- https://github.com/input-output-hk/cardano-sl/blob/429efc2426c63802ae86789f5b828dcbb42de88a/wallet/src/Pos/Util/Mnemonics.hs#L66-L87
--
cardanoSlSeed :: forall n csz mw . ConsistentEntropy n mw csz
              => Proxy n
              -> MnemonicSentence mw
              -> Maybe Seed
cardanoSlSeed _ mw =
    case wordsToEntropy @n @csz @mw mw of
        Left _ -> Nothing
        Right e -> Just $ BA.convert $ toCbor $ blake2b $ toCbor (entropyRaw e)
  where blake2b :: ByteString -> Digest Blake2b_256
        blake2b = hash

        toCbor :: BA.ByteArrayAccess ba => ba -> ByteString
        toCbor bs
            | len < 24    = BA.cons (0x40 + fromIntegral len) $ BA.convert bs
            | len < 0x100 = BA.cons 0x58 $ BA.cons (fromIntegral len) $ BA.convert bs
            | otherwise   = error "we do not support entropy of length > 256 bytes"
          where
            len = BA.length bs
