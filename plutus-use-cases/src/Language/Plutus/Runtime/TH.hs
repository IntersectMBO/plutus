{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
-- | Useful functions for validator scripts, in the form of quoted expressions
module Language.Plutus.Runtime.TH(
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

import           Language.Haskell.TH        (Exp, Q)
import qualified Language.PlutusTx.Builtins as Builtins
import           Wallet.UTXO.Runtime

import           Prelude                    (Bool (..), Eq (..), Int, Maybe (..))

-- | Logical AND
and :: Q Exp
and = [| \(l :: Bool) (r :: Bool) -> if l then r else False |]

-- | Logical OR
or :: Q Exp
or = [| \(l :: Bool) (r :: Bool) -> if l then True else r |]

-- | Logical negation
not :: Q Exp
not = [| \(a :: Bool) -> if a then False else True  |]

-- | The smaller of two `Int`s
min :: Q Exp
min = [| \(a :: Int) (b :: Int) -> if a < b then a else b |]

-- | The larger of two `Int`s
max :: Q Exp
max = [| \(a :: Int) (b :: Int) -> if a > b then a else b |]

-- | Check if a transaction was signed by a public key
txSignedBy :: Q Exp
txSignedBy = [|
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
    |]

-- | Check if the input of a pending transaction was signed by a public key
txInSignedBy :: Q Exp
txInSignedBy = [|
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

    |]

isJust :: Q Exp
isJust = [| \(m :: Maybe a) -> case m of { Just _ -> True; _ -> False; } |]

isNothing :: Q Exp
isNothing = [| \(m :: Maybe a) -> case m of { Just _ -> False; }  |]

maybe :: Q Exp
maybe = [| \b f m ->
    case m of
        Nothing -> b
        Just a  -> f a |]

map :: Q Exp
map = [|
    \f l ->
        let go ls = case ls of
                x:xs -> f x : go xs
                _    -> []
        in go l
        |]

foldr :: Q Exp
foldr = [|
    \f b l ->
        let go cur as = case as of
                []    -> cur
                a:as' -> go (f a cur) as'
        in go b l
    |]

length :: Q Exp
length = [|
    \l ->
        -- it would be nice to define length in terms of foldr,
        -- but we can't, due to staging restrictions.
        let go lst = case lst of
                []   -> 0::Int
                _:xs -> 1 + go xs
        in go l
    |]

all :: Q Exp
all = [|
    \pred l ->
        let go lst = case lst of
                []   -> True
                x:xs -> pred x && go xs
        in go l
    |]

-- | Returns the public key that locks the transaction output
pubKeyOutput :: Q Exp
pubKeyOutput = [| \(o:: PendingTxOut) -> case o of
    PendingTxOut _ _ (PubKeyTxOut pk) -> Just pk
    _                                 -> Nothing |]

-- | Returns the data script that is part of the pay-to-script transaction
--   output
scriptOutput :: Q Exp
scriptOutput = [| \(o:: PendingTxOut) -> case o of
    PendingTxOut _ d DataTxOut -> d
    _                          -> Nothing |]

-- | Equality of public keys
eqPubKey :: Q Exp
eqPubKey = [| \(PubKey l) (PubKey r) -> l == r |]

-- | Equality of data scripts
eqDataScript :: Q Exp
eqDataScript = [| \(DataScriptHash l) (DataScriptHash r) -> Builtins.equalsByteString l r |]

-- | Equality of validator scripts
eqValidator :: Q Exp
eqValidator = [| \(ValidatorHash l) (ValidatorHash r) -> Builtins.equalsByteString l r |]

-- | Equality of redeemer scripts
eqRedeemer :: Q Exp
eqRedeemer = [| \(RedeemerHash l) (RedeemerHash r) -> Builtins.equalsByteString l r |]

eqTx :: Q Exp
eqTx = [| \(TxHash l) (TxHash r) -> Builtins.equalsByteString l r |]
