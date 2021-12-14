{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Crypto.Wallet.Pure
    ( XPrv(..)
    , XPub(..)
    , xprvPub
    , deriveXPrv
    , deriveXPrvHardened
    , deriveXPub
    , hInitSeed
    , hFinalize
    ) where

import           Control.DeepSeq             (NFData)
import qualified Crypto.Math.Edwards25519    as Edwards25519
import           Crypto.Hash                 (SHA512)
import qualified Crypto.MAC.HMAC             as HMAC
--import qualified Crypto.PubKey.Ed25519       as Ed25519
import           Data.Bits
import           Data.ByteArray              (ByteArrayAccess, convert)
import qualified Data.ByteArray              as B (splitAt)
import           Data.ByteString             (ByteString)
import qualified Data.ByteString             as B (pack)
import           Data.Hashable               (Hashable)
import           Data.Word
import           GHC.Generics                (Generic)

import           Cardano.Crypto.Wallet.Types

data XPrv = XPrv !Edwards25519.Scalar !ChainCode

data XPub = XPub !Edwards25519.PointCompressed !ChainCode
    deriving (Eq, Ord, Show, Generic)

instance NFData XPub
instance Hashable XPub

xprvPub :: XPrv -> ByteString
xprvPub (XPrv s _) =
    Edwards25519.unPointCompressed $ Edwards25519.scalarToPoint s

deriveXPrv :: XPrv -> Word32 -> XPrv
deriveXPrv (XPrv sec ccode) n =
    let !pub     = Edwards25519.scalarToPoint sec
        (iL, iR) = walletHash $ DerivationHashNormal pub ccode n
        !derived = Edwards25519.scalar iL
     in XPrv (Edwards25519.scalarAdd sec derived) iR

deriveXPrvHardened :: XPrv -> Word32 -> XPrv
deriveXPrvHardened (XPrv sec ccode) n =
    let (iL, iR) = walletHash $ DerivationHashHardened sec ccode n
     in XPrv (Edwards25519.scalar iL) iR

-- | Derive a child public from an extended public key
deriveXPub :: XPub -> Word32 -> XPub
deriveXPub (XPub pub ccode) n =
    let (iL, iR) = walletHash $ DerivationHashNormal pub ccode n
        !derived = Edwards25519.scalarToPoint $ Edwards25519.scalar iL
     in XPub (Edwards25519.pointAdd pub derived) iR


-- hashing methods either hardened or normal
data DerivationHash where
    DerivationHashHardened :: Edwards25519.Scalar          -> ChainCode -> Word32 -> DerivationHash
    DerivationHashNormal   :: Edwards25519.PointCompressed -> ChainCode -> Word32 -> DerivationHash

walletHash :: DerivationHash -> (ByteString, ChainCode)
walletHash (DerivationHashHardened sec cc w) =
    hFinalize
            $ flip HMAC.update (encodeIndex w)
            $ flip HMAC.update (Edwards25519.unScalar sec)
            $ flip HMAC.update hardenedTag
            $ hInit cc
walletHash (DerivationHashNormal pub cc w) =
    hFinalize
            $ flip HMAC.update (encodeIndex w)
            $ flip HMAC.update (Edwards25519.unPointCompressed pub)
            $ flip HMAC.update normalTag
            $ hInit cc

hardenedTag :: ByteString
hardenedTag = B.pack $ map (fromIntegral . fromEnum) "HARD"
normalTag :: ByteString
normalTag   = B.pack $ map (fromIntegral . fromEnum) "NORM"

-- | Encode a Word32 in Big endian
encodeIndex :: Word32 -> ByteString
encodeIndex w = B.pack [d,c,b,a]
  where
    a = fromIntegral w
    b = fromIntegral (w `shiftR` 8)
    c = fromIntegral (w `shiftR` 16)
    d = fromIntegral (w `shiftR` 24)

hInit :: ChainCode -> HMAC.Context SHA512
hInit (ChainCode key) = HMAC.initialize key

hInitSeed :: ByteArrayAccess seed => seed -> HMAC.Context SHA512
hInitSeed seed = HMAC.initialize seed

hFinalize :: HMAC.Context SHA512 -> (ByteString, ChainCode)
hFinalize ctx =
    let (b1, b2) = B.splitAt 32 $ convert $ HMAC.finalize ctx
     in (b1, ChainCode b2)
