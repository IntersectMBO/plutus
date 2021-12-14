{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import           Control.Monad
import           GHC.TypeLits

import           Basement.From
import           Basement.Nat
import           Basement.Bounded
import           Foundation.Collection (nonEmpty_)
import           Foundation (IsList(..))
import           Foundation.Check
import           Foundation.Check.Main

import qualified Crypto.Math.Edwards25519 as Edwards25519
import qualified Crypto.ECC.Ed25519Donna as EdVariant

import qualified Crypto.ECC.Ed25519BIP32 as EdBIP32

import           Cardano.Crypto.Wallet
import           Cardano.Crypto.Wallet.Encrypted
import qualified Cardano.Crypto.Wallet.Pure as PureWallet
import qualified Data.ByteString as B
import qualified Data.ByteArray as B (convert)
import           Crypto.Error
import           Crypto.Random (drgNewTest, withDRG)
import qualified Crypto.Random as Random
import           Crypto.Math.Bits
import qualified Crypto.Math.Bytes as Bytes
import           Data.Word
import           Data.Bits
import           Data.Monoid ((<>))
import           Data.Proxy

import           Data.Type.Equality
import           Utils

import qualified Crypto.Encoding.BIP39 as BIP39
import qualified Cardano.Crypto.Encoding.Seed as PW

import qualified Test.Crypto as Crypto
import qualified Test.Cardano as Cardano

noPassphrase :: B.ByteString
noPassphrase = ""

dummyPassphrase :: B.ByteString
dummyPassphrase = "dummy passphrase"

newtype Passphrase = Passphrase B.ByteString
    deriving (Show,Eq)

data Ed = Ed Integer Edwards25519.Scalar

newtype Seed = Seed B.ByteString
    deriving (Show,Eq)

newtype ValidSeed = ValidSeed Seed
    deriving (Show,Eq)

newtype Message = Message B.ByteString
    deriving (Show,Eq)

newtype Salt = Salt B.ByteString
    deriving (Show,Eq)

p :: Integer
p = 2^(255 :: Int) - 19

q :: Integer
q = 2^(252 :: Int) + 27742317777372353535851937790883648493

chooseInt :: forall n . KnownNat n => Proxy n -> Gen Int
chooseInt _ = fromInteger . from . unZn <$> (arbitrary :: Gen (Zn n))

chooseInteger :: forall n . KnownNat n => Integer -> Proxy n -> Gen Integer
chooseInteger base _ = ((+) base) . fromInteger . from . unZn <$> (arbitrary :: Gen (Zn n))

instance Show Ed where
    show (Ed i _) = "Edwards25519.Scalar " <> show i
instance Eq Ed where
    (Ed x _) == (Ed y _) = x == y
instance Arbitrary Ed where
    arbitrary = do
        n <- frequency $ nonEmpty_
                [ (1, chooseInteger (q-10000) (Proxy :: Proxy 9999))
                , (1, chooseInteger 1         (Proxy :: Proxy 999))
                , (2, chooseInteger 1         (Proxy :: Proxy 7237005577332262213973186563042994240857116359379907606001950938285454250988))
                ]
        return (Ed n (Edwards25519.scalarFromInteger n))
instance Arbitrary Message where
    arbitrary = Message . B.pack <$> (chooseInt (Proxy :: Proxy 10) >>= \n -> replicateM n arbitrary)
instance Arbitrary Salt where
    arbitrary = Salt . B.pack <$> (chooseInt (Proxy :: Proxy 10) >>= \n -> replicateM n arbitrary)
instance Arbitrary Passphrase where
    arbitrary = Passphrase . B.pack <$> (chooseInt (Proxy :: Proxy 23) >>= \n -> replicateM n arbitrary)
instance Arbitrary Seed where
    arbitrary = Seed . B.pack <$> replicateM 32 arbitrary
instance Arbitrary ValidSeed where
    arbitrary = do
        s@(Seed seed) <- arbitrary
        case seedToSecret seed of
            CryptoPassed _ -> pure $ ValidSeed s
            _              -> arbitrary

testEdwards25519 =
    [ Property "add" $ \(Ed _ a) (Ed _ b) -> (ltc a .+ ltc b) == ltc (Edwards25519.scalarAdd a b)
    ]
  where
    (.+) = Edwards25519.pointAdd
    ltc = Edwards25519.scalarToPoint

testPointAdd =
    [ Property "add" $ \(Ed _ a) (Ed _ b) ->
        let pa = Edwards25519.scalarToPoint a
            pb = Edwards25519.scalarToPoint b
            pc = Edwards25519.pointAdd pa pb
            pa' = pointToPublic pa
            pb' = pointToPublic pb
            pc' = EdVariant.publicAdd pa' pb'
         in Edwards25519.unPointCompressed pc === B.convert pc'
    ]

{-
testHdDerivation =
    [ Property "pub . sec-derivation = pub-derivation . pub" normalDerive
    , Property "verify (pub . pub-derive) (sign . sec-derivation)" verifyDerive
    ]
  where
    dummyChainCode = B.replicate 32 38
    dummyMsg = B.pack [1,2,3,4,5,6,7]

    normalDerive (Ed _ s) n =
        let pubKey = Edwards25519.scalarToPoint s
            prv = either error id $ xprv (Edwards25519.unScalar s `B.append` Edwards25519.unPointCompressed pubKey `B.append` dummyChainCode)
            pub = toXPub prv
            cPrv = deriveXPrv noPassphrase prv n
            cPub = deriveXPub pub n
         in unXPub (toXPub cPrv) === unXPub cPub

    verifyDerive (Ed _ s) n =
        let pubKey = Edwards25519.scalarToPoint s
            prv = either error id $ xprv (Edwards25519.unScalar s `B.append` Edwards25519.unPointCompressed pubKey `B.append` dummyChainCode)
            pub = toXPub prv
            cPrv = deriveXPrv noPassphrase prv n
            cPub = deriveXPub pub n
         in verify cPub dummyMsg (sign noPassphrase cPrv dummyMsg)
-}

testEncrypted =
    [ Property "pub(sec) = pub(encrypted(no-pass, sec))" (pubEq noPassphrase)
    , Property "pub(sec) = pub(encrypted(dummy, sec))" (pubEq dummyPassphrase)
    , Property "pub(sec) = pub(encrypted(no-pass, sec))" (pubEqValid noPassphrase)
    , Property "pub(sec) = pub(encrypted(dummy, sec))" (pubEqValid dummyPassphrase)
    , Property "sign(sec, msg) = sign(encrypted(no-pass, sec), msg)" (signEq noPassphrase)
    , Property "sign(sec, msg) = sign(encrypted(dummy, sec), msg)" (signEq dummyPassphrase)
    , Property "n <= 0x80000000 => pub(derive(sec, n)) = derive-public(pub(sec), n) [chaincode]" (deriveNormalChainCode noPassphrase)
    , Property "n <= 0x80000000 => pub(derive(sec, n)) = derive-public(pub(sec), n) [publickey]" (deriveNormalPublicKey dummyPassphrase)
    {-
    , Property "derive-hard(sec, n) = derive-hard(encrypted(no-pass, sec), n)" (deriveEq True noPassphrase)
    , Property "derive-hard(sec, n) = derive-hard(encrypted(dummy, sec), n)" (deriveEq True dummyPassphrase)
    , Property "derive-norm(sec, n) = derive-norm(encrypted(no-pass, sec), n)" (deriveEq False noPassphrase)
    , Property "derive-norm(sec, n) = derive-norm(encrypted(dummy, sec), n)" (deriveEq False dummyPassphrase)
    -}
    ]
  where
    dummyChainCode = B.replicate 32 38
    pubEq pass (Seed s) =
        let a    = seedToSecret s
            pub1 = EdVariant.toPublic <$> a
            ekey = encryptedCreate s pass dummyChainCode
         in (B.convert <$> pub1) === (encryptedPublic <$> ekey)
    pubEqValid pass (ValidSeed (Seed s)) =
        case (seedToSecret s, encryptedCreate s pass dummyChainCode) of
            (CryptoPassed a, CryptoPassed ekey) ->
                let pub1 = EdVariant.toPublic a
                 in B.convert pub1 === encryptedPublic ekey
            _ -> error "valid seed got a invalid result"

    signEq pass (ValidSeed (Seed s)) (Message msg) =
        case (seedToSecret s, encryptedCreate s pass dummyChainCode) of
            (CryptoPassed a, CryptoPassed ekey) ->
                let pub1 = EdVariant.toPublic a
                    sig1 = EdVariant.sign a dummyChainCode pub1 msg
                    (Signature sig2) = encryptedSign ekey pass msg
                 in B.convert sig1 === sig2
            _ -> error "valid seed got a invalid result"
    deriveNormalPublicKey pass dscheme (ValidSeed (Seed s)) nRaw =
        let ekey = throwCryptoError $ encryptedCreate s pass dummyChainCode
            ckey = encryptedDerivePrivate dscheme ekey pass n
            (expectedPubkey, expectedChainCode) = encryptedDerivePublic dscheme (encryptedPublic ekey, encryptedChainCode ekey) n
         in encryptedPublic ckey === expectedPubkey
      where n = nRaw `mod` 0x80000000
    deriveNormalChainCode pass dscheme (ValidSeed (Seed s)) nRaw =
        let ekey = throwCryptoError $ encryptedCreate s pass dummyChainCode
            ckey = encryptedDerivePrivate dscheme ekey pass n
            (expectedPubkey, expectedChainCode) = encryptedDerivePublic dscheme (encryptedPublic ekey, encryptedChainCode ekey) n
         in encryptedChainCode ckey === expectedChainCode
      where n = nRaw `mod` 0x80000000
            {-
    deriveEq True pass (Seed s) n =
        let a     = scalarToSecret s
            xprv1 = flip PureWallet.XPrv (ChainCode dummyChainCode) <$> s
            cprv1 = PureWallet.deriveXPrvHardened xprv1 n
            xprv2 = encryptedCreate s pass dummyChainCode
            cprv2 = encryptedDeriveHardened xprv2 pass n
         in PureWallet.xprvPub cprv1 === (encryptedPublic <$> cprv2)
    deriveEq False pass (Seed s) n =
        let a     = scalarToSecret s
            xprv1 = PureWallet.XPrv s (ChainCode dummyChainCode)
            cprv1 = PureWallet.deriveXPrv xprv1 n
            xprv2 = encryptedCreate s pass dummyChainCode
            cprv2 = encryptedDeriveNormal xprv2 pass n
         in PureWallet.xprvPub cprv1 === encryptedPublic cprv2
         -}

testVariant =
    [ Property "public-key" testPublicKey
    , Property "signature" testSignature
    , Property "scalar-add" testScalarAdd
    -- , Property "point-add" testPointAdd
    ]
  where
    testPublicKey (Ed _ a) =
        let pub1 = Edwards25519.scalarToPoint a
            pub2 = EdVariant.toPublic (scalarToSecret a)
         in pub1 `pointEqPublic` pub2
    testSignature (Ed _ a) (Salt salt) (Message msg) =
        let -- pub = Edwards25519.unPointCompressed $ Edwards25519.scalarToPoint a
            sec = scalarToSecret a
            sig1 = Edwards25519.sign a salt msg
            sig2 = EdVariant.sign sec salt (EdVariant.toPublic sec) msg
         in sig1 `signatureEqSig` sig2
    testScalarAdd (Ed _ a) (Ed _ b) =
        let r1 = Edwards25519.scalarAdd a b
            r2 = EdVariant.secretAdd (scalarToSecret a) (scalarToSecret b)
         in r1 `scalarEqSecret` r2
    testPointAdd (Ed _ a) (Ed _ b) =
        let p = Edwards25519.scalarToPoint a
            q = Edwards25519.scalarToPoint b
            p' = EdVariant.toPublic $ scalarToSecret a
            q' = EdVariant.toPublic $ scalarToSecret b
         in Edwards25519.pointAdd p q `pointEqPublic` EdVariant.publicAdd p' q'

    signatureEqSig :: Edwards25519.Signature -> EdVariant.Signature -> PropertyCheck
    signatureEqSig sig sig2 = Edwards25519.unSignature sig === B.convert sig2

    pointEqPublic :: Edwards25519.PointCompressed -> EdVariant.PublicKey -> PropertyCheck
    pointEqPublic pub (EdVariant.PublicKey pub2) = Edwards25519.unPointCompressed pub === B.convert pub2

    scalarEqSecret :: Edwards25519.Scalar -> EdVariant.SecretKey -> PropertyCheck
    scalarEqSecret s sec = Edwards25519.unScalar s === B.convert sec

pointToPublic :: Edwards25519.PointCompressed -> EdVariant.PublicKey
pointToPublic = throwCryptoError . EdVariant.publicKey . Edwards25519.unPointCompressed

scalarToSecret :: Edwards25519.Scalar -> EdVariant.SecretKey
scalarToSecret = throwCryptoError . EdVariant.secretKey . Edwards25519.unScalar

testChangePassphrase :: [Test]
testChangePassphrase =
    [ Property "change-passphrase-publickey-stable" pubEq
    , Property "normal-derive-key-different-passphrase-stable" deriveNormalEq
    , Property "hardened-derive-key-different-passphrase-stable" deriveHardenedEq
    ]
  where
    pubEq (ValidSeed (Seed s)) (Passphrase p1) (Passphrase p2) =
        let xprv1 = throwCryptoError $ encryptedCreate s p1 dummyChainCode
            xprv2 = encryptedChangePass p1 p2 xprv1
         in encryptedPublic xprv1 === encryptedPublic xprv2

    deriveNormalEq dscheme (ValidSeed (Seed s)) (Passphrase p1) (Passphrase p2) n =
        let xprv1 = throwCryptoError $ encryptedCreate s p1 dummyChainCode
            xprv2 = encryptedChangePass p1 p2 xprv1
            cPrv1 = encryptedDerivePrivate dscheme xprv1 p1 (toNormal n)
            cPrv2 = encryptedDerivePrivate dscheme xprv2 p2 (toNormal n)
         in encryptedPublic cPrv1 === encryptedPublic cPrv2

    deriveHardenedEq dscheme (ValidSeed (Seed s)) (Passphrase p1) (Passphrase p2) n =
        let xprv1 = throwCryptoError $ encryptedCreate s p1 dummyChainCode
            xprv2 = encryptedChangePass p1 p2 xprv1
            cPrv1 = encryptedDerivePrivate dscheme xprv1 p1 (toHardened n)
            cPrv2 = encryptedDerivePrivate dscheme xprv2 p2 (toHardened n)
         in encryptedPublic cPrv1 === encryptedPublic cPrv2

    dummyChainCode = B.replicate 32 38

    toHardened, toNormal :: Word32 -> Word32
    toHardened n = setBit n 31
    toNormal   n = clearBit n 31

seedToSecret :: B.ByteString -> CryptoFailable EdVariant.SecretKey
seedToSecret = EdVariant.secretKey

series :: String -> [a] -> (a -> Test) -> Test
series cmd l runProp = Group (fromList cmd) $ map runProp l

withHardIndex :: Integer
              -> (forall n . (KnownNat n, EdBIP32.ValidDerivationIndex n ~ 'True, EdBIP32.ValidDerivationHardIndex n ~ 'True)
                  => EdBIP32.DerivationIndex 'EdBIP32.Hard n
                  -> Test)
              -> Test
withHardIndex idxVal f =
    case someNatVal idxVal of
        Just (SomeNat (pidx :: Proxy n)) ->
            case EdBIP32.getValidIndex pidx of
                Nothing   -> error ("invalid index: " ++ show idxVal)
                Just Refl ->
                    case EdBIP32.getValidHardIndex pidx of
                        Nothing   -> error ("invalid hard index: " ++ show idxVal)
                        Just Refl -> f (EdBIP32.DerivationIndex :: EdBIP32.DerivationIndex 'EdBIP32.Hard n)
        Nothing ->
            error "not a known number"

withSoftIndex :: Integer
              -> (forall n . (KnownNat n, EdBIP32.ValidDerivationIndex n ~ 'True, EdBIP32.ValidDerivationSoftIndex n ~ 'True)
                  => EdBIP32.DerivationIndex 'EdBIP32.Soft n
                  -> Test)
              -> Test
withSoftIndex idxVal f =
    case someNatVal idxVal of
        Just (SomeNat (pidx :: Proxy n)) ->
            case EdBIP32.getValidIndex pidx of
                Nothing   -> error ("invalid index: " ++ show idxVal)
                Just Refl ->
                    case EdBIP32.getValidSoftIndex pidx of
                        Nothing   -> error ("invalid soft index: " ++ show idxVal)
                        Just Refl -> f (EdBIP32.DerivationIndex :: EdBIP32.DerivationIndex 'EdBIP32.Soft n)
        Nothing ->
            error "not a known number"

testEdBIP32 :: [Test]
testEdBIP32 =
    [ Property "Xprv creation" $ \rsk rcc ->
        let extPriv = makeXprv rsk rcc
            k       = makeEdBip32 rsk rcc
         in xprvEqKey extPriv k
    , Property "pub same" $ \rsk rcc ->
        let extPriv = makeXprv rsk rcc
            k       = makeEdBip32 rsk rcc
         in xprvEqPublicKey (toXPub extPriv) (EdBIP32.toPublic k)
    , series "verify-hard-secret-derivation" hardIdx $ \idx ->
        withHardIndex idx $ \hIdx ->
            Property (fromList $ show idx) $ \rsk rcc ->
                let extPriv = makeXprv rsk rcc
                    cPrv1   = deriveXPrv DerivationScheme2 noPassphrase extPriv (fromIntegral idx)
                    k       = makeEdBip32 rsk rcc
                    cK      = EdBIP32.derive hIdx k
                 in xprvEqKey cPrv1 cK
    , series "verify-soft-secret-derivation" softIdx $ \idx ->
        withSoftIndex idx $ \hIdx ->
            Property (fromList $ show idx) $ \rsk rcc ->
                let extPriv = makeXprv rsk rcc
                    cPrv1   = deriveXPrv DerivationScheme2 noPassphrase extPriv (fromIntegral idx)
                    k       = makeEdBip32 rsk rcc
                    cK      = EdBIP32.derive hIdx k
                 in xprvEqKey cPrv1 cK
    ]
  where

    makeEdBip32 (RandomSecretKey k) (RandomChainCode cc) =
        let (s1,s2)  = B.splitAt 32 k
         in (packN s1, packN s2, EdBIP32.ChainCode $ packBytesN cc)

    softIdx = [1..9]
    hardIdx = [0x80000000..0x80000003] ++ [0xf00f0001..0xf00f0004] ++ [0x90000003..0x90000005]

    xprvEqKey :: XPrv -> EdBIP32.Key -> Bool
    xprvEqKey xPrv (k1,k2,EdBIP32.ChainCode cc) =
        -- xprv is 64 bits of secret key, 32 bits of public key and 32 bits of chain code
        let (s1, r1) = B.splitAt 32 $ B.convert xPrv
            (s2, r2) = B.splitAt 32 r1
            (_p , c) = B.splitAt 32 r2
         in assertEq "chain code" (B.unpack c) (Bytes.unpack cc) &&
            assertEq "key2" (B.unpack s2) (Bytes.unpack $ Bytes.fromBits Bytes.LittleEndian k2) &&
            assertEq "key1" (B.unpack s1) (Bytes.unpack $ Bytes.fromBits Bytes.LittleEndian k1)

    xprvEqPublicKey :: XPub -> EdBIP32.Public -> Bool
    xprvEqPublicKey xPub (point, EdBIP32.ChainCode cc) =
        assertEq "point" (B.unpack $ xpubPublicKey xPub) (Bytes.unpack $ Bytes.fromBits Bytes.LittleEndian point) &&
        assertEq "public chain code" (B.unpack $ B.convert $ xpubChaincode xPub) (Bytes.unpack cc)

    assertEq s l1 l2
        | l1 /= l2  = error ("expected Eq for " ++ s ++ "\n" ++ "  wallet: " ++ dumpRaw l1 ++ "\n  alt   : " ++ dumpRaw l2)
        | otherwise = True


    packN :: B.ByteString -> FBits 256
    packN = Bytes.toBits Bytes.LittleEndian . Bytes.pack . B.unpack

    packBytesN :: B.ByteString -> Bytes.Bytes 32
    packBytesN = Bytes.pack . B.unpack

    --unpackN :: KnownNat n => FBits n -> B.ByteString
    --unpackN = B.pack . binFromFBits

-- -------------------------------------------------------------------------- --
--                              Main                                          --
-- -------------------------------------------------------------------------- --

main :: IO ()
main = defaultMain $ Group "cardano-crypto"
    [ Group "edwards25519-arithmetic" testEdwards25519
    , Group "edwards25519-BIP32" testEdBIP32
    , Group "point-addition" testPointAdd
    , Group "encrypted" testEncrypted
    , Group "change-pass" testChangePassphrase
    , Crypto.tests
    , Cardano.tests
    ]
    {-
    , Group "edwards25519-ed25519variant" testVariant
    , Group "hd-derivation" testHdDerivation
    ]
    -}
