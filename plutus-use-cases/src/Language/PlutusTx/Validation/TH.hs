{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
-- | Useful functions for validator scripts, in the form of quoted expressions
module Language.PlutusTx.Validation.TH(
    -- * Boolean operators
    and,
    or,
    not,
    -- * Numbers
    min,
    max,
    -- * Maybe
    isJust,
    isNothing,
    maybe,
    -- * Lists
    map,
    foldr,
    length,
    all,
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

import           Prelude                    (Bool (..), Eq (..), Int, Maybe (..), (<), (>), (+))

-- | Logical AND
and :: Q (TExp (Bool -> Bool -> Bool))
and = [|| \(l :: Bool) (r :: Bool) -> if l then r else False ||]

-- | Logical OR
or :: Q (TExp (Bool -> Bool -> Bool))
or = [|| \(l :: Bool) (r :: Bool) -> if l then True else r ||]

-- | Logical negation
not :: Q (TExp (Bool -> Bool))
not = [|| \(a :: Bool) -> if a then False else True  ||]

-- | The smaller of two `Int`s
min :: Q (TExp (Int -> Int -> Int))
min = [|| \(a :: Int) (b :: Int) -> if a < b then a else b ||]

-- | The larger of two `Int`s
max :: Q (TExp (Int -> Int -> Int))
max = [|| \(a :: Int) (b :: Int) -> if a > b then a else b ||]

-- | Check if a transaction was signed by a public key
txSignedBy :: Q (TExp (PendingTx ValidatorHash -> PubKey -> Bool))
txSignedBy = [||
    \(p :: PendingTx ValidatorHash) (PubKey k) ->
        let
            PendingTx _ _ _ _ _ sigs _ = p

            signedBy :: Signature -> Bool
            signedBy (Signature s) = s == k

            go :: [Signature] -> Bool
            go l = case l of
                        s:r -> if signedBy s then True else go r
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

            signedBy :: Signature -> Bool
            signedBy (Signature i') = i' == k

            go :: [Signature] -> Bool
            go l = case l of
                        s:r -> if signedBy s then True else go r
                        []  -> False
        in go sigs

    ||]

isJust :: Q (TExp (Maybe a -> Bool))
isJust = [|| \(m :: Maybe a) -> case m of { Just _ -> True; _ -> False; } ||]

isNothing :: Q (TExp (Maybe a -> Bool))
isNothing = [|| \(m :: Maybe a) -> case m of { Just _ -> False; } ||]

maybe :: Q (TExp (b -> (a -> b) -> Maybe a -> b))
maybe = [|| \b f m ->
    case m of
        Nothing -> b
        Just a  -> f a ||]

map :: Q (TExp ((a -> b) -> [a] -> [b]))
map = [||
    \f l ->
        let go ls = case ls of
                x:xs -> f x : go xs
                _    -> []
        in go l
        ||]

foldr :: Q (TExp ((a -> b -> b) -> b -> [a] -> b))
foldr = [||
    \f b l ->
        let go cur as = case as of
                []    -> cur
                a:as' -> go (f a cur) as'
        in go b l
    ||]

length :: Q (TExp ([a] -> Int))
length = [||
    \l ->
        -- it would be nice to define length in terms of foldr,
        -- but we can't, due to staging restrictions.
        let go lst = case lst of
                []   -> 0::Int
                _:xs -> 1 + go xs
        in go l
    ||]

all :: Q (TExp ((a -> Bool) -> [a] -> Bool))
all = [||
    \pred l ->
        let and a b = if a then b else False
            go lst = case lst of
                []   -> True
                x:xs -> pred x `and` go xs
        in go l
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
