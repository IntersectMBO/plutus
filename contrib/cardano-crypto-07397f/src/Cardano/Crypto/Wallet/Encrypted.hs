module Cardano.Crypto.Wallet.Encrypted
    ( EncryptedKey
    , encryptedKey
    , unEncryptedKey
    , Signature(..)
    -- * Methods
    , encryptedCreate
    , encryptedCreateDirectWithTweak
    , encryptedChangePass
    , encryptedSign
    , encryptedPublic
    , encryptedChainCode
    , encryptedDerivePrivate
    , encryptedDerivePublic
    ) where

import           Control.DeepSeq
import           Data.Word
import           Foreign.C.Types
import           Foreign.Ptr

import           Crypto.Error
import           Data.ByteArray   (ByteArrayAccess, withByteArray)
import qualified Data.ByteArray   as B
import           Data.ByteString  (ByteString)
import           System.IO.Unsafe

import           Cardano.Crypto.Wallet.Types (DerivationScheme(..), DerivationIndex)

totalKeySize :: Int
totalKeySize = encryptedKeySize + publicKeySize + ccSize

--totalPublicKeySize :: Int
--totalPublicKeySize = publicKeySize + ccSize

encryptedKeySize :: Int
encryptedKeySize = 64

publicKeySize :: Int
publicKeySize = 32

ccSize :: Int
ccSize = 32

signatureSize :: Int
signatureSize = 64

publicKeyOffset :: Int
publicKeyOffset = encryptedKeySize

ccOffset :: Int
ccOffset = publicKeyOffset + publicKeySize

newtype Signature = Signature ByteString
    deriving (NFData)

newtype EncryptedKey = EncryptedKey ByteString
    deriving (NFData, ByteArrayAccess)

type PublicKey = ByteString
type ChainCode = ByteString

data PassPhrase

-- | Create an encryped key from binary representation.
--
-- If the binary is not of the right size, Nothing is returned
encryptedKey :: ByteString -> Maybe EncryptedKey
encryptedKey ba
    | B.length ba == totalKeySize = Just $ EncryptedKey ba
    | otherwise                   = Nothing

unEncryptedKey :: EncryptedKey -> ByteString
unEncryptedKey (EncryptedKey e) = e

-- | Create a new encrypted key from the secret, encrypting the secret in memory
-- using the passphrase.
encryptedCreate :: (ByteArrayAccess passphrase, ByteArrayAccess secret, ByteArrayAccess cc)
                => secret
                -> passphrase
                -> cc
                -> CryptoFailable EncryptedKey
encryptedCreate sec pass cc
    | B.length sec /= 32 = CryptoFailed CryptoError_SecretKeySizeInvalid
    | otherwise          = unsafePerformIO $ do
        (r, k) <- B.allocRet totalKeySize $ \ekey ->
            withByteArray sec  $ \psec  ->
            withByteArray pass $ \ppass ->
            withByteArray cc   $ \pcc   ->
                wallet_encrypted_from_secret ppass (fromIntegral $ B.length pass) psec pcc ekey
        if r == 0
            then return $ CryptoPassed $ EncryptedKey k
            else return $ CryptoFailed CryptoError_SecretKeyStructureInvalid

-- | Create a new encrypted key using the output of the masterKeyGeneration directly (96 bytes)
-- using the encryption passphrase.
encryptedCreateDirectWithTweak :: (ByteArrayAccess passphrase, ByteArrayAccess secret)
                               => secret
                               -> passphrase
                               -> EncryptedKey
encryptedCreateDirectWithTweak sec pass =
    EncryptedKey $ B.allocAndFreeze totalKeySize $ \ekey ->
        withByteArray sec  $ \psec  ->
        withByteArray pass $ \ppass ->
            wallet_encrypted_new_from_mkg ppass (fromIntegral $ B.length pass) psec ekey

-- | Create a new encrypted key that uses a different passphrase
encryptedChangePass :: (ByteArrayAccess oldPassPhrase, ByteArrayAccess newPassPhrase)
                    => oldPassPhrase -- ^ passphrase to decrypt the current encrypted key
                    -> newPassPhrase -- ^ new passphrase to use for the new encrypted key
                    -> EncryptedKey  -- ^ Key using the old pass phrase
                    -> EncryptedKey  -- ^ Key using the new pass phrase
encryptedChangePass oldPass newPass (EncryptedKey okey) =
    EncryptedKey $ B.allocAndFreeze totalKeySize $ \ekey ->
        withByteArray oldPass $ \opass  ->
        withByteArray newPass $ \npass  ->
        withByteArray okey    $ \oldkey ->
            wallet_encrypted_change_pass oldkey
                         opass (fromIntegral $ B.length oldPass)
                         npass (fromIntegral $ B.length newPass)
                         ekey

-- | Sign using the encrypted keys and temporarly decrypt the secret in memory
-- with a minimal memory footprint.
encryptedSign :: (ByteArrayAccess passphrase, ByteArrayAccess msg)
              => EncryptedKey
              -> passphrase
              -> msg
              -> Signature
encryptedSign (EncryptedKey ekey) pass msg =
    Signature $ B.allocAndFreeze signatureSize $ \sig ->
        withByteArray ekey $ \k ->
        withByteArray pass $ \p ->
        withByteArray msg  $ \m ->
            wallet_encrypted_sign k p (fromIntegral $ B.length pass) m (fromIntegral $ B.length msg) sig

encryptedDerivePrivate :: (ByteArrayAccess passphrase)
                       => DerivationScheme
                       -> EncryptedKey
                       -> passphrase
                       -> DerivationIndex
                       -> EncryptedKey
encryptedDerivePrivate dscheme (EncryptedKey parent) pass childIndex =
    EncryptedKey $ B.allocAndFreeze totalKeySize $ \ekey ->
        withByteArray pass   $ \ppass   ->
        withByteArray parent $ \pparent ->
            wallet_encrypted_derive_private pparent ppass (fromIntegral $ B.length pass) childIndex ekey (dschemeToC dscheme)

encryptedDerivePublic :: DerivationScheme
                      -> (PublicKey, ChainCode)
                      -> DerivationIndex
                      -> (PublicKey, ChainCode)
encryptedDerivePublic dscheme (pub, cc) childIndex
    | childIndex >= 0x80000000 = error "cannot derive hardened in derive public"
    | otherwise                = unsafePerformIO $ do
        (newCC, newPub) <-
                B.allocRet publicKeySize $ \outPub ->
                B.alloc ccSize           $ \outCc  ->
                withByteArray pub        $ \ppub   ->
                withByteArray cc         $ \pcc    -> do
                    r <- wallet_encrypted_derive_public ppub pcc childIndex outPub outCc (dschemeToC dscheme)
                    if r /= 0 then error "encrypted derive public assumption about index failed" else return ()
        return (newPub, newCC)

-- | Get the public part of an encrypted key
encryptedPublic :: EncryptedKey -> ByteString
encryptedPublic (EncryptedKey ekey) = sub publicKeyOffset publicKeySize ekey

-- | Get the chain code part of an encrypted key
encryptedChainCode :: EncryptedKey -> ByteString
encryptedChainCode (EncryptedKey ekey) = sub ccOffset ccSize ekey

sub :: B.ByteArray c => Int -> Int -> c -> c
sub ofs sz = B.take sz . B.drop ofs

-- map to the C enum : derivation_scheme_mode
type CDerivationScheme = CInt

dschemeToC :: DerivationScheme -> CDerivationScheme
dschemeToC DerivationScheme1 = 1
dschemeToC DerivationScheme2 = 2

-- return 0 if success, otherwise 1 if structure of seed not proper
foreign import ccall "wallet_encrypted_from_secret"
    wallet_encrypted_from_secret :: Ptr PassPhrase -> Word32
                                 -> Ptr Word8 -- 32 bytes "seed secret key" (non extended)
                                 -> Ptr Word8 -- 32 bytes ChainCode
                                 -> Ptr EncryptedKey
                                 -> IO CInt

foreign import ccall "wallet_encrypted_new_from_mkg"
    wallet_encrypted_new_from_mkg :: Ptr PassPhrase -> Word32
                                  -> Ptr Word8 -- 96 bytes master key generation
                                  -> Ptr EncryptedKey
                                  -> IO ()

foreign import ccall "wallet_encrypted_sign"
    wallet_encrypted_sign :: Ptr EncryptedKey
                          -> Ptr PassPhrase -> Word32
                          -> Ptr Word8 -> Word32
                          -> Ptr Signature
                          -> IO ()

foreign import ccall "wallet_encrypted_derive_private"
    wallet_encrypted_derive_private :: Ptr EncryptedKey
                                    -> Ptr PassPhrase -> Word32
                                    -> DerivationIndex -- index
                                    -> Ptr EncryptedKey
                                    -> CDerivationScheme
                                    -> IO ()

foreign import ccall "wallet_encrypted_derive_public"
    wallet_encrypted_derive_public :: Ptr PublicKey
                                   -> Ptr ChainCode
                                   -> DerivationIndex
                                   -> Ptr PublicKey
                                   -> Ptr ChainCode
                                   -> CDerivationScheme
                                   -> IO CInt

foreign import ccall "wallet_encrypted_change_pass"
    wallet_encrypted_change_pass :: Ptr EncryptedKey
                                 -> Ptr PassPhrase -> Word32
                                 -> Ptr PassPhrase -> Word32
                                 -> Ptr EncryptedKey
                                 -> IO ()
