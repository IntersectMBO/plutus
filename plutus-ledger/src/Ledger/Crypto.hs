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
    , passPhrase
    ) where

import qualified Cardano.Crypto.Wallet   as Crypto
import           Crypto.Hash             as Crypto
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
      $ BA.convert @_ @BS.ByteString
      $ Crypto.hashWith Crypto.Blake2b_224 (fromBuiltin bs)

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
