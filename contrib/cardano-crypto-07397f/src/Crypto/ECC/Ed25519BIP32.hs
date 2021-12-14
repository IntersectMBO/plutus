{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE GADTs                 #-}
module Crypto.ECC.Ed25519BIP32 where

import qualified Crypto.Hash as C (SHA512, SHA256)
import qualified Crypto.MAC.HMAC as C
import qualified Data.ByteArray as B
import qualified Data.ByteString as BS
import           Data.Bits
import           Data.Kind (Type)
import           Data.Word
import           Data.Proxy
import qualified Crypto.Math.Edwards25519 as ED25519
import           Data.Type.Bool
import           Data.Type.Equality
import           GHC.TypeLits
import           Data.Function (on)
import           Unsafe.Coerce (unsafeCoerce)

import           Crypto.Math.Bits
import           Crypto.Math.Bytes (Bytes)
import qualified Crypto.Math.Bytes as Bytes

-- | A Master secret is a 256 bits random quantity
type MasterSecret = FBits 256

-- | A child key is similar to the key in structure
-- except it has an additional annotation representing
-- the indexes for the hierarchy derivation indexes from
-- a base 'Key' (usually the root key)
type ChildKey (didxs :: DerivationHier) = Key

-- | A key is a 512 bit random value and a chaincode
--
-- Left half need to have:
-- * Lowest 3 bits clear
-- * Highest bit clear
-- * Second highest bit set
-- * Third highest bit clear
--
-- Right half doesn't have any particular structure.
type Key = (FBits 256, FBits 256, ChainCode)

-- | A public part of a key
type Public = (PointCompressed, ChainCode)

-- | A point is 1 bit of x sign and 255 bit of y coordinate (y's 256th bit is always 0)
type PointCompressed = FBits 256

-- | A 256 bits chain code
newtype ChainCode = ChainCode { unChainCode :: Bytes 32 }
    deriving (Eq)

-- | A n bits Digest
newtype Hash n = Hash { unHash :: FBits n }
    deriving (Eq)

-- | A Serialized tag used during HMAC
type Tag = Bytes 1

-- | Serialized Index
newtype SerializedIndex = SerializedIndex (Bytes 4)
    deriving (Eq)

type HMAC_SHA512 = Bytes 64

data DerivationType = Hard | Soft
data DerivationMaterial = ChainCodeMaterial | KeyMaterial

data DerivationIndex (k :: DerivationType) (n :: Nat) = DerivationIndex

data DerivationHier = (:>) Nat DerivationHier | DerivationEnd

type MaxHardIndex = 0xffffffff
type MinHardIndex = 0x80000000
type MaxSoftIndex = MinHardIndex - 1
type MinSoftIndex = 0

data ValidIndex :: Nat -> Type where
    IsValidIndex    :: (ValidDerivationIndex n :~: 'True) -> ValidIndex n
    IsNotValidIndex :: (ValidDerivationIndex n :~: 'False) -> ValidIndex n

data ValidHardIndex :: Nat -> Type where
    IsValidHardIndex    :: (ValidDerivationHardIndex n :~: 'True) -> ValidHardIndex n
    IsNotValidHardIndex :: (ValidDerivationHardIndex n :~: 'False) -> ValidHardIndex n

data ValidSoftIndex :: Nat -> Type where
    IsValidSoftIndex    :: (ValidDerivationSoftIndex n :~: 'True) -> ValidSoftIndex n
    IsNotValidSoftIndex :: (ValidDerivationSoftIndex n :~: 'False) -> ValidSoftIndex n

getValidIndex :: KnownNat n => Proxy n -> Maybe (ValidDerivationIndex n :~: 'True)
getValidIndex n = case isValidIndex n of
                    IsValidIndex Refl -> Just Refl
                    _                 -> Nothing

isValidIndex :: KnownNat n => Proxy n -> ValidIndex n
isValidIndex n
    |  natVal (Proxy @MinSoftIndex) <= natVal n
    && natVal n <= natVal (Proxy @MaxHardIndex) = IsValidIndex (unsafeCoerce Refl)
    | otherwise                                 = IsNotValidIndex (unsafeCoerce Refl)

getValidHardIndex :: KnownNat n => Proxy n -> Maybe (ValidDerivationHardIndex n :~: 'True)
getValidHardIndex n = case isValidHardIndex n of
                    IsValidHardIndex Refl -> Just Refl
                    _                     -> Nothing

isValidHardIndex :: KnownNat n => Proxy n -> ValidHardIndex n
isValidHardIndex n
    |  natVal (Proxy @MinHardIndex) <= natVal n
    && natVal n <= natVal (Proxy @MaxHardIndex) = IsValidHardIndex (unsafeCoerce Refl)
    | otherwise                                 = IsNotValidHardIndex (unsafeCoerce Refl)

getValidSoftIndex :: KnownNat n => Proxy n -> Maybe (ValidDerivationSoftIndex n :~: 'True)
getValidSoftIndex n = case isValidSoftIndex n of
                    IsValidSoftIndex Refl -> Just Refl
                    _                     -> Nothing

isValidSoftIndex :: KnownNat n => Proxy n -> ValidSoftIndex n
isValidSoftIndex n
    |  natVal (Proxy @MinSoftIndex) <= natVal n
    && natVal n <= natVal (Proxy @MaxSoftIndex) = IsValidSoftIndex (unsafeCoerce Refl)
    | otherwise                                 = IsNotValidSoftIndex (unsafeCoerce Refl)

type ValidDerivationIndex     (n :: Nat) = (MinSoftIndex <=? n) && (n <=? MaxHardIndex)
type ValidDerivationHardIndex (n :: Nat) = (MinHardIndex <=? n) && (n <=? MaxHardIndex)
type ValidDerivationSoftIndex (n :: Nat) = (MinSoftIndex <=? n) && (n <=? MaxSoftIndex)

type family ValidDerivationIndexForType (k :: DerivationType) (n :: Nat) :: Bool where
    ValidDerivationIndexForType 'Hard n = ValidDerivationHardIndex n
    ValidDerivationIndexForType 'Soft n = ValidDerivationSoftIndex n

type family DerivationTag (ty :: DerivationType) (material :: DerivationMaterial) :: Nat where
    DerivationTag 'Hard 'KeyMaterial       = 0x0
    DerivationTag 'Hard 'ChainCodeMaterial = 0x1
    DerivationTag 'Soft 'KeyMaterial       = 0x2
    DerivationTag 'Soft 'ChainCodeMaterial = 0x3

-- | Check if the left half is valid
leftHalfValid :: FBits 256 -> Bool
leftHalfValid v =
    and [ testBit v 0 == False
        , testBit v 1 == False
        , testBit v 2 == False
        , testBit v 29 == False
        , testBit v 28 == True
        , testBit v 31 == False
        ]

toPublic :: Key -> Public
toPublic (kl, _, cc) = (kToPoint kl, cc)

kToPoint :: FBits 256 -> PointCompressed
kToPoint k = pointFromRepr $ ED25519.scalarToPoint r
  where r = ED25519.scalarP $ Bytes.fromBits Bytes.LittleEndian k

pointAdd :: PointCompressed -> PointCompressed -> PointCompressed
pointAdd = ((pointFromRepr . ) .  ED25519.pointAdd) `on` pointToRepr

pointToRepr :: PointCompressed -> ED25519.PointCompressed
pointToRepr a = ED25519.pointCompressedP $ Bytes.fromBits Bytes.LittleEndian a

pointFromRepr :: ED25519.PointCompressed -> PointCompressed
pointFromRepr =
      Bytes.toBits Bytes.LittleEndian
    . ED25519.unPointCompressedP

type family BitsToHashScheme (n :: Nat) where
    BitsToHashScheme 256 = C.SHA256
    BitsToHashScheme 512 = C.SHA512

type ValidTag tag = (0 <= tag, tag <= 3)

-- | Compute the HMAC-SHA512 using the ChainCode as the key
fcp :: forall tag idx deriveType deriveMaterial
     . ( KnownNat (DerivationTag deriveType deriveMaterial)
       , KnownNat idx
       , (DerivationTag deriveType deriveMaterial) ~ tag
       , ValidDerivationIndex idx ~ 'True
       , ValidDerivationIndexForType deriveType idx ~ 'True
       )
    => Proxy deriveMaterial
    -> Proxy deriveType
    -> Proxy idx
    -> ChainCode
    -> DerivationIndex deriveType idx
    -> [Word8]
    -> HMAC_SHA512
fcp _ _ pidx c _ input =
    hmacSHA512 key `Bytes.packSome` (Bytes.unpack tagValue ++ input ++ Bytes.unpack idx)
  where
    key = unChainCode c

    (SerializedIndex idx) = indexSerialized pidx

    tagValue :: Tag
    tagValue = Bytes.pack [fromIntegral $ natVal (Proxy :: Proxy tag)]

hmacSHA512 :: Bytes keyLength -> Bytes input -> HMAC_SHA512
hmacSHA512 key ({-Bytes.trace "hmac-input" ->-} msg) =
    Bytes.pack $ B.unpack $ C.hmacGetDigest computed
  where
    computed :: C.HMAC C.SHA512
    computed = C.hmac (BS.pack $ Bytes.unpack key) (BS.pack $ Bytes.unpack msg)

class GetDerivationMaterial (dtype :: DerivationType) mat where
    getDerivationMaterial :: Proxy dtype -> mat -> [Word8]
instance GetDerivationMaterial 'Soft Key where
    getDerivationMaterial p key = getDerivationMaterial p (fst $ toPublic key)
instance GetDerivationMaterial 'Hard Key where
    getDerivationMaterial _ (kl,kr,_) =
        Bytes.unpack $ Bytes.append (Bytes.fromBits Bytes.LittleEndian kl)
                                    (Bytes.fromBits Bytes.LittleEndian kr)
instance GetDerivationMaterial 'Soft PointCompressed where
    getDerivationMaterial _ p = Bytes.unpack $ Bytes.fromBits Bytes.LittleEndian p

derive :: forall dtype idx .
          ( KnownNat (DerivationTag dtype 'KeyMaterial)
          , KnownNat (DerivationTag dtype 'ChainCodeMaterial)
          , KnownNat idx
          , ValidDerivationIndex idx ~ 'True
          , ValidDerivationIndexForType dtype idx ~ 'True
          , GetDerivationMaterial dtype Key)
       => DerivationIndex dtype idx
       -> Key
       -> Key
derive idx key@(kl, kr, c) = (kl', kr', c')
  where
    dtype       = Proxy :: Proxy dtype
    matKeyProxy = Proxy :: Proxy 'KeyMaterial
    matCCProxy  = Proxy :: Proxy 'ChainCodeMaterial
    -- 1) Z
    z = fcp matKeyProxy dtype (Proxy :: Proxy idx) c idx
            (getDerivationMaterial dtype key)

    -- 2) produce kl' and kr'
    (zl8, zr) = step2 z

    kl' = zl8 + kl
    kr' = zr + kr

    -- 3) child chain code
    untrimmedCC = fcp matCCProxy dtype (Proxy :: Proxy idx) c idx
                      (getDerivationMaterial dtype key)
    c' = ChainCode $ Bytes.drop untrimmedCC

derivePublic :: forall idx dtype .
          ( dtype ~ 'Soft -- can only derive public stuff with Soft Derivation
          , KnownNat (DerivationTag dtype 'KeyMaterial)
          , KnownNat (DerivationTag dtype 'ChainCodeMaterial)
          , KnownNat idx
          , ValidDerivationIndex idx ~ 'True
          , ValidDerivationIndexForType dtype idx ~ 'True
          , GetDerivationMaterial dtype PointCompressed)
       => DerivationIndex 'Soft idx
       -> PointCompressed
       -> ChainCode
       -> (PointCompressed, ChainCode)
derivePublic idx p c = (p', c')
  where
    dtype       = Proxy :: Proxy dtype
    matKeyProxy = Proxy :: Proxy 'KeyMaterial
    matCCProxy  = Proxy :: Proxy 'ChainCodeMaterial
    -- 1) Z
    z = fcp matKeyProxy dtype (Proxy :: Proxy idx) c idx (getDerivationMaterial dtype p)

    -- 2) produce kl' and kr'
    (zl8, _) = step2 z

    p' = kToPoint zl8 `pointAdd` p

    -- 3) child chain code
    untrimmedCC = fcp matCCProxy dtype (Proxy :: Proxy idx) c idx
                      (getDerivationMaterial dtype p)
    c' = ChainCode $ Bytes.drop untrimmedCC

-- | Given Z, return 8*ZL(28Bytes) and ZR
step2 :: Bytes 64 -> (FBits 256, FBits 256)
step2 z = (8 * zeroExtendedZl, Bytes.toBits Bytes.LittleEndian zRight)
  where
    (zLeft32, zRight) = Bytes.splitHalf z

    -- step
    -- * take 28 bytes of zLeft32 (zl)
    -- * extend back to 32 bytes
    -- * multiply this number by 8
    zeroExtendedZl = zeroExtender `append` Bytes.toBits Bytes.LittleEndian zl

    zl :: Bytes 28 -- only take 28 bytes
    zl = Bytes.take zLeft32

    zeroExtender :: FBits (4*8) -- re-extend by 4 bytes
    zeroExtender = 0

-- | Serialized index
indexSerialized :: forall idx . (KnownNat idx, ValidDerivationIndex idx ~ 'True)
                => Proxy idx
                -> SerializedIndex
indexSerialized idx = SerializedIndex $ Bytes.fromBits Bytes.LittleEndian (fromInteger n :: FBits 32)
  where n = natVal idx
