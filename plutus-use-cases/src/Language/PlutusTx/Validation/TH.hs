{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
-- | Useful functions for validator scripts, in the form of quoted expressions
module Language.PlutusTx.Validation.TH(
    -- * Signatures
    txSignedBy,
    txInSignedBy,
    -- * Transactions
    pubKeyOutput,
    scriptOutput,
    eqPubKey,
    eqDataScript,
    eqRedeemer,
    eqValidator,
    eqTx
    ) where

import           Language.Haskell.TH        (Q, TExp)
import qualified Language.PlutusTx.Builtins as Builtins
import           Ledger
import           Ledger.Validation

import           Prelude                    (Bool (..), Eq (..), Maybe (..))

-- | Check if a transaction was signed by a public key
txSignedBy :: Q (TExp (PendingTx ValidatorHash -> PubKey -> Bool))
txSignedBy = [||
    \(p :: PendingTx ValidatorHash) (PubKey k) ->
        let
            PendingTx _ _ _ _ _ sigs _ = p

            signedBy' :: Signature -> Bool
            signedBy' (Signature s) = s == k

            go :: [Signature] -> Bool
            go l = case l of
                        s:r -> if signedBy' s then True else go r
                        []  -> False
        in
            go sigs
    ||]

-- | Check if the input of a pending transaction was signed by a public key
txInSignedBy :: Q (TExp (PendingTxIn -> PubKey -> Bool))
txInSignedBy = [||
    \(i :: PendingTxIn) (PubKey k) ->
        let
            PendingTxIn ref _ _      = i
            PendingTxOutRef _ _ sigs = ref

            signedBy' :: Signature -> Bool
            signedBy' (Signature i') = i' == k

            go :: [Signature] -> Bool
            go l = case l of
                        s:r -> if signedBy' s then True else go r
                        []  -> False
        in go sigs

    ||]

-- | Returns the public key that locks the transaction output
pubKeyOutput :: Q (TExp (PendingTxOut -> Maybe PubKey))
pubKeyOutput = [|| \(o:: PendingTxOut) -> case o of
    PendingTxOut _ _ (PubKeyTxOut pk) -> Just pk
    _                                 -> Nothing ||]

-- | Returns the data script that is part of the pay-to-script transaction
--   output
scriptOutput :: Q (TExp (PendingTxOut -> Maybe (ValidatorHash, DataScriptHash)))
scriptOutput = [|| \(o:: PendingTxOut) -> case o of
    PendingTxOut _ d DataTxOut -> d
    _                          -> Nothing ||]

-- | Equality of public keys
eqPubKey :: Q (TExp (PubKey -> PubKey -> Bool))
eqPubKey = [|| \(PubKey l) (PubKey r) -> l == r ||]

-- | Equality of data scripts
eqDataScript :: Q (TExp (DataScriptHash -> DataScriptHash -> Bool))
eqDataScript = [|| \(DataScriptHash l) (DataScriptHash r) -> Builtins.equalsByteString l r ||]

-- | Equality of validator scripts
eqValidator :: Q (TExp (ValidatorHash -> ValidatorHash -> Bool))
eqValidator = [|| \(ValidatorHash l) (ValidatorHash r) -> Builtins.equalsByteString l r ||]

-- | Equality of redeemer scripts
eqRedeemer :: Q (TExp (RedeemerHash -> RedeemerHash -> Bool))
eqRedeemer = [|| \(RedeemerHash l) (RedeemerHash r) -> Builtins.equalsByteString l r ||]

-- | Equality of transactions
eqTx :: Q (TExp (TxHash -> TxHash -> Bool))
eqTx = [|| \(TxHash l) (TxHash r) -> Builtins.equalsByteString l r ||]
