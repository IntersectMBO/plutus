{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Ledger.Crypto
    ( module Export
    , PrivateKey
    , pubKeyHash
    , signedBy
    , sign
    , signTx
    , generateFromSeed
    , toPublicKey
    , xPubToPublicKey
    -- $privateKeys
    , knownPrivateKeys
    , privateKey1
    , privateKey2
    , privateKey3
    , privateKey4
    , privateKey5
    , privateKey6
    , privateKey7
    , privateKey8
    , privateKey9
    , privateKey10
    ) where

import           Cardano.Crypto.Hash     as Crypto
import qualified Cardano.Crypto.Wallet   as Crypto
import qualified Data.ByteArray          as BA
import qualified Data.ByteString         as BS
import           Plutus.V1.Ledger.Api
import qualified Plutus.V1.Ledger.Bytes  as KB
import           Plutus.V1.Ledger.Crypto as Export hiding (PrivateKey)
import qualified PlutusTx.Prelude        as P

type PrivateKey = Crypto.XPrv

-- | Compute the hash of a public key.
pubKeyHash :: PubKey -> PubKeyHash
pubKeyHash (PubKey (LedgerBytes bs)) =
    PubKeyHash
      $ toBuiltin
      $ Crypto.hashToBytes
      $ Crypto.hashWith @Crypto.Blake2b_224 id (fromBuiltin bs)

-- | Check whether the given 'Signature' was signed by the private key corresponding to the given public key.
signedBy :: Signature -> PubKey -> TxId -> Bool
signedBy (Signature s) (PubKey k) (TxId txId) =
    let xpub = Crypto.XPub (KB.bytes k) (Crypto.ChainCode "" {- value is ignored -})
        xsig = either error id $ Crypto.xsignature (P.fromBuiltin s)
    in Crypto.verify xpub txId xsig

-- | Sign the hash of a transaction using a private key.
signTx :: TxId -> Crypto.XPrv -> Signature
signTx (TxId txId) = sign txId

-- | Sign a message using a private key.
sign :: BA.ByteArrayAccess a => a -> Crypto.XPrv -> Signature
sign msg privKey = Signature . toBuiltin . Crypto.unXSignature $ Crypto.sign passPhrase privKey msg

passPhrase :: BS.ByteString
passPhrase = "Ledger.Crypto PassPhrase"

generateFromSeed :: BS.ByteString -> Crypto.XPrv
generateFromSeed seed = Crypto.generate seed passPhrase

xPubToPublicKey :: Crypto.XPub -> PubKey
xPubToPublicKey = PubKey . KB.fromBytes . Crypto.xpubPublicKey

toPublicKey :: Crypto.XPrv -> PubKey
toPublicKey = xPubToPublicKey . Crypto.toXPub

-- $privateKeys
-- 'privateKey1', 'privateKey2', ... 'privateKey10' are ten predefined 'PrivateKey' values.
--
-- The private keys can be found in the 'sign.input' file linked from
-- http://ed25519.cr.yp.to/software.html.

privateKey1, privateKey2, privateKey3, privateKey4, privateKey5, privateKey6, privateKey7, privateKey8, privateKey9, privateKey10 :: Crypto.XPrv
privateKey1 = generateFromSeed "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
privateKey2 = generateFromSeed "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c"
privateKey3 = generateFromSeed "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025"
privateKey4 = generateFromSeed "0d4a05b07352a5436e180356da0ae6efa0345ff7fb1572575772e8005ed978e9e61a185bcef2613a6c7cb79763ce945d3b245d76114dd440bcf5f2dc1aa57057"
privateKey5 = generateFromSeed "6df9340c138cc188b5fe4464ebaa3f7fc206a2d55c3434707e74c9fc04e20ebbc0dac102c4533186e25dc43128472353eaabdb878b152aeb8e001f92d90233a7"
privateKey6 = generateFromSeed "b780381a65edf8b78f6945e8dbec7941ac049fd4c61040cf0c324357975a293ce253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01"
privateKey7 = generateFromSeed "78ae9effe6f245e924a7be63041146ebc670dbd3060cba67fbc6216febc44546fbcfbfa40505d7f2be444a33d185cc54e16d615260e1640b2b5087b83ee3643d"
privateKey8 = generateFromSeed "691865bfc82a1e4b574eecde4c7519093faf0cf867380234e3664645c61c5f7998a5e3a36e67aaba89888bf093de1ad963e774013b3902bfab356d8b90178a63"
privateKey9 = generateFromSeed "3b26516fb3dc88eb181b9ed73f0bcd52bcd6b4c788e4bcaf46057fd078bee073f81fb54a825fced95eb033afcd64314075abfb0abd20a970892503436f34b863"
privateKey10 = generateFromSeed "edc6f5fbdd1cee4d101c063530a30490b221be68c036f5b07d0f953b745df192c1a49c66e617f9ef5ec66bc4c6564ca33de2a5fb5e1464062e6d6c6219155efd"

-- | A list of 10 private keys.
--   TODO: Generate random private keys (I couldn't find a way to
--         do this in 'Crypto.ECC.Ed25519Donna' in 'cardano-crypto')
knownPrivateKeys :: [Crypto.XPrv]
knownPrivateKeys = [privateKey1, privateKey2, privateKey3, privateKey4, privateKey5, privateKey6, privateKey7, privateKey8, privateKey9, privateKey10]

