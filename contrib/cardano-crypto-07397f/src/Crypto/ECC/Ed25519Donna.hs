-- |
-- Module      : Crypto.PubKey.Ed25519
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : unknown
--
-- Ed25519 support
--
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}
module Crypto.ECC.Ed25519Donna
    ( SecretKey(..)
    , PublicKey(..)
    , Signature
    -- * Smart constructors
    , signature
    , publicKey
    , secretKey
    -- * methods
    , toPublic
    , sign
    , verify
    , publicAdd
    , secretAdd
    ) where

import           Control.DeepSeq
import           Data.Word
import           Foreign.Ptr
import           Foreign.C.Types

import           Data.ByteArray (ByteArrayAccess, withByteArray, ScrubbedBytes, Bytes)
import qualified Data.ByteArray as B
import           Crypto.Error
import           Foreign.Storable
import           System.IO.Unsafe
import           Crypto.Hash (hashWith, SHA512(..))
import           Data.ByteArray (alloc)
import           Data.Bits
import           Control.Monad

unsafeDoIO :: IO a -> a
unsafeDoIO = unsafeDupablePerformIO
{-# NOINLINE unsafeDoIO #-}

-- | An Ed25519 Secret key
newtype SecretKey = SecretKey ScrubbedBytes
    deriving (Eq,ByteArrayAccess,NFData)

-- | An Ed25519 public key
newtype PublicKey = PublicKey Bytes
    deriving (Show,Eq,ByteArrayAccess,NFData)

-- | An Ed25519 signature
newtype Signature = Signature Bytes
    deriving (Show,Eq,ByteArrayAccess,NFData)

-- | Try to build a public key from a bytearray
publicKey :: ByteArrayAccess ba => ba -> CryptoFailable PublicKey
publicKey bs
    | B.length bs == publicKeySize =
        CryptoPassed $ PublicKey $ B.copyAndFreeze bs (\_ -> return ())
    | otherwise =
        CryptoFailed $ CryptoError_PublicKeySizeInvalid

-- | Try to build a secret key from a bytearray
secretKey :: ByteArrayAccess ba => ba -> CryptoFailable SecretKey
secretKey bs
    | B.length bs == 32 = unsafePerformIO verifyAndTweak
    | otherwise         = CryptoFailed CryptoError_SecretKeySizeInvalid
  where
    k = hashWith SHA512 bs
    verifyAndTweak :: IO (CryptoFailable SecretKey)
    verifyAndTweak = withByteArray k $ \inp -> do
        b0  <- peekElemOff inp 0 :: IO Word8
        b31 <- peekElemOff inp 31
        if testBit b31 5
            then return $ CryptoFailed CryptoError_SecretKeyStructureInvalid
            else CryptoPassed . SecretKey <$> (alloc 64 $ \outp -> do
                    pokeElemOff outp 0 (b0 .&. 0xf8) -- clear lowest 3 bits
                    forM_ [1..30] $ \i -> peekElemOff inp i >>= pokeElemOff outp i
                    pokeElemOff outp 31 ((b31 .&. 0x1f) .|. 0x40) -- clear highest bit and 3rd bit, and set 2nd highest.
                    forM_ [32..63] $ \i -> peekElemOff inp i >>= pokeElemOff outp i
                    )

-- | Try to build a signature from a bytearray
signature :: ByteArrayAccess ba => ba -> CryptoFailable Signature
signature bs
    | B.length bs == signatureSize =
        CryptoPassed $ Signature $ B.copyAndFreeze bs (\_ -> return ())
    | otherwise =
        -- missing a SignatureSizeInvalid error, so use another one
        CryptoFailed $ CryptoError_SecretKeySizeInvalid

-- | Create a public key from a secret key
toPublic :: SecretKey -> PublicKey
toPublic (SecretKey sec) = PublicKey $
    B.allocAndFreeze publicKeySize $ \result ->
    withByteArray sec              $ \psec   ->
        ccryptonite_ed25519_publickey psec result
{-# NOINLINE toPublic #-}

publicAdd :: PublicKey -> PublicKey -> PublicKey
publicAdd p1 p2 =
    PublicKey $ B.allocAndFreeze publicKeySize $ \result ->
        withByteArray p1 $ \v1 ->
        withByteArray p2 $ \v2 ->
            ccryptonite_ed25519_point_add v1 v2 result

secretAdd :: SecretKey -> SecretKey -> SecretKey
secretAdd p1 p2 =
    SecretKey $ B.allocAndFreeze secretKeySize $ \result ->
        withByteArray p1 $ \v1 ->
        withByteArray p2 $ \v2 ->
            ccryptonite_ed25519_scalar_add v1 v2 result

-- | Sign a message using the key pair
sign :: (ByteArrayAccess msg, ByteArrayAccess salt) => SecretKey -> salt -> PublicKey -> msg -> Signature
sign secret salt public message =
    Signature $ B.allocAndFreeze signatureSize $ \sig ->
        withByteArray secret  $ \sec   ->
        withByteArray public  $ \pub   ->
        withByteArray salt    $ \saltP ->
        withByteArray message $ \msg   ->
             ccryptonite_ed25519_sign msg (fromIntegral msgLen) saltP (fromIntegral saltLen) sec pub sig
  where
    !msgLen  = B.length message
    !saltLen = B.length salt

-- | Verify a message
verify :: ByteArrayAccess ba => PublicKey -> ba -> Signature -> Bool
verify public message signatureVal = unsafeDoIO $
    withByteArray signatureVal $ \sig ->
    withByteArray public       $ \pub ->
    withByteArray message      $ \msg -> do
      r <- ccryptonite_ed25519_sign_open msg (fromIntegral msgLen) pub sig
      return (r == 0)
  where
    !msgLen = B.length message

publicKeySize :: Int
publicKeySize = 32

secretKeySize :: Int
secretKeySize = 64

signatureSize :: Int
signatureSize = 64

foreign import ccall "cardano_crypto_ed25519_publickey"
    ccryptonite_ed25519_publickey :: Ptr SecretKey -- secret key
                                  -> Ptr PublicKey -- public key
                                  -> IO ()

foreign import ccall "cardano_crypto_ed25519_sign_open"
    ccryptonite_ed25519_sign_open :: Ptr Word8     -- message
                                  -> CSize         -- message len
                                  -> Ptr PublicKey -- public
                                  -> Ptr Signature -- signature
                                  -> IO CInt

foreign import ccall "cardano_crypto_ed25519_sign"
    ccryptonite_ed25519_sign :: Ptr Word8     -- message
                             -> CSize         -- message len
                             -> Ptr Word8     -- salt
                             -> CSize         -- salt len
                             -> Ptr SecretKey -- secret
                             -> Ptr PublicKey -- public
                             -> Ptr Signature -- signature
                             -> IO ()

foreign import ccall "cardano_crypto_ed25519_point_add"
    ccryptonite_ed25519_point_add :: Ptr PublicKey -- p1
                                  -> Ptr PublicKey -- p2
                                  -> Ptr PublicKey -- p1 + p2
                                  -> IO ()

foreign import ccall "cardano_crypto_ed25519_scalar_add"
    ccryptonite_ed25519_scalar_add :: Ptr SecretKey -- s1
                                   -> Ptr SecretKey -- s2
                                   -> Ptr SecretKey -- s1 + s2
                                   -> IO ()
