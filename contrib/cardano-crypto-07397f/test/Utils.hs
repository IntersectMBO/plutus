module Utils
    ( RandomSecretKey(..)
    , RandomChainCode(..)
    , HardIdx(..)
    , SoftIdx(..)
    -- * Functions helper
    , makeXprv
    , rskToScalar
    , dumpRaw
    ) where

import           Data.Word
import           Data.Bits
import qualified Data.ByteString as B
import           Control.Monad
import qualified Crypto.Math.Edwards25519 as Edwards25519
import           Cardano.Crypto.Wallet (XPrv, xprv)

import           Foundation.Check

-- | Randomly generated ED25519 Extended secret key (64 bytes with a special structure)
newtype RandomSecretKey = RandomSecretKey B.ByteString
    deriving (Eq)

instance Show RandomSecretKey where
    show (RandomSecretKey bs) = "RandomSecretKey " ++ (dumpRaw $ B.unpack bs)

instance Arbitrary RandomSecretKey where
    arbitrary =  do
        {-
        high     <- toHigh <$> pure 0
        middle   <- replicateM 30 (pure 0)
        low      <- toLow <$> pure 0
        extended <- replicateM 32 (pure 0)
        -}

        high     <- toHigh <$> arbitrary
        middle   <- replicateM 30 arbitrary
        low      <- toLow <$> arbitrary
        extended <- replicateM 32 arbitrary
        pure $ RandomSecretKey $ B.pack $ [low] ++ middle ++ [high] ++ extended
      where
        toHigh w = w `clearBit` 7 `clearBit` 5 `setBit` 6
        toLow w = w `clearBit` 0 `clearBit` 1 `clearBit` 2


-- | Randomly generate chain code (32 bytes)
newtype RandomChainCode = RandomChainCode B.ByteString
    deriving (Eq)

instance Show RandomChainCode where
    show (RandomChainCode bs) = "RandomChainCode " ++ (dumpRaw $ B.unpack bs)

instance Arbitrary RandomChainCode where
    arbitrary = RandomChainCode . B.pack <$> {-pure (replicate 32 0) <$>-} replicateM 32 arbitrary

newtype HardIdx = HardIdx Word32
    deriving (Show,Eq)

instance Arbitrary HardIdx where
    arbitrary = HardIdx . setBit 31 <$> arbitrary

newtype SoftIdx = SoftIdx Word32
    deriving (Show,Eq)

instance Arbitrary SoftIdx where
    arbitrary = SoftIdx . clearBit 31 <$> arbitrary

makeXprv :: RandomSecretKey -> RandomChainCode -> XPrv
makeXprv (RandomSecretKey k) (RandomChainCode cc) =
    let (s1,s2)  = B.splitAt 32 k
        scalar   = Edwards25519.scalar s1
        pub      = Edwards25519.scalarToPoint scalar
        xprvData = k `B.append` Edwards25519.unPointCompressed pub `B.append` cc
     in either (error "makeXprv: invalid") id $ xprv xprvData

rskToScalar :: RandomSecretKey -> Edwards25519.Scalar
rskToScalar (RandomSecretKey rsk) = Edwards25519.scalar (B.take 32 rsk)

hex :: Int -> Char
hex 0  = '0'
hex 1  = '1'
hex 2  = '2'
hex 3  = '3'
hex 4  = '4'
hex 5  = '5'
hex 6  = '6'
hex 7  = '7'
hex 8  = '8'
hex 9  = '9'
hex 10 = 'a'
hex 11 = 'b'
hex 12 = 'c'
hex 13 = 'd'
hex 14 = 'e'
hex 15 = 'f'
hex _  = ' '

{-# INLINE hexBytes #-}
hexBytes :: Word8 -> (Char, Char)
hexBytes w = (hex h, hex l) where (h,l) = (fromIntegral w) `divMod` 16

-- | Dump one byte into a 2 hexadecimal characters.
hexString :: Word8 -> String
hexString i = [h,l] where (h,l) = hexBytes i

-- | Dump a list of word8 into a raw string of hex value
dumpRaw :: [Word8] -> String
dumpRaw = concatMap hexString

