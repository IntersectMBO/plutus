{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeOperators       #-}
-- Set -O0 to make it a fairer fight
{-# OPTIONS_GHC -O0 #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module Main (main) where

import           Prelude                                           hiding (tail)

import           Control.Lens.Indexed
import           Criterion.Main
import           Crypto.Hash
import qualified Data.ByteArray                                    as BA
import qualified Data.ByteString                                   as BS
import qualified Data.ByteString.Lazy                              as BSL
import qualified Language.PlutusTx.Coordination.Contracts.MultiSig as MS
import qualified Language.PlutusTx.Prelude                         as P
import           Ledger
import qualified Ledger.Crypto                                     as Crypto
import           LedgerBytes
import           Wallet

import qualified Language.PlutusTx                                 as PlutusTx
import qualified Language.PlutusTx.Prelude                         as PlutusTx
import           Language.PlutusTx.Evaluation                      (unsafeEvaluateCek)

import qualified Recursion                                         as Rec
import qualified Scott                                             as Scott
import Opt

main :: IO ()
main = defaultMain [ functions, validators ]

-- | Execution of some interesting functions.
functions :: Benchmark
functions = bgroup "functions" [ verifySignatureB, hashB, fibB, sumB, tailB ]

-- | Execution of signature verification, which is something that the validating nodes will have
-- to do frequently, and typically >1 time per transaction.
verifySignatureB :: Benchmark
verifySignatureB = bgroup "verifySignature" (imap (\i d -> bench ("verifySignature-" <> show i) $ nf verifySignature d) signatureData)
    where
        signatureData :: [(PubKey, Digest SHA256, Signature)]
        signatureData =
            [ ( pk1 , txHash , sig1)
            , ( pk2 , txHash , sig2)
            ]

-- | Hashing is also potentially expensive.
hashB :: Benchmark
hashB = bgroup "hash" (imap (\i d -> bench ("hash-" <> show i) $ nf hashit d) hashData)
    where
        -- TODO: check that this is the right hash function to check against
        hashit :: BS.ByteString -> Digest SHA256
        hashit = hash
        hashData :: [BS.ByteString]
        hashData = ["", "looooooooooooooooooooooooooooooooooooooooooooooooong"]

-- | The fibonnaci function.
fibB :: Benchmark
fibB = bgroup "fib" [
        bgroup "5" [
            bench "plutus" $ nf unsafeEvaluateCek (PlutusTx.getPlc $$(PlutusTx.compile [|| fib 5 ||])),
            bench "plutus-opt" $ nf unsafeEvaluateCek (PlutusTx.getPlc $$(PlutusTx.compile [|| fibOpt 5 ||])),
            bench "native" $ nf fib 5,
            bench "combinator" $ nf fibRec 5
        ],
        bgroup "10" [
            bench "plutus" $ nf unsafeEvaluateCek (PlutusTx.getPlc $$(PlutusTx.compile [|| fib 10 ||])),
            bench "plutusOpt" $ nf unsafeEvaluateCek (PlutusTx.getPlc $$(PlutusTx.compile [|| fibOpt 10 ||])),
            bench "native" $ nf fib 10,
            bench "combinator" $ nf fibRec 10
        ]
    ]
    where
        fib :: Integer -> Integer
        fib n =
            if n P.== 0
            then 0
            else if n P.== 1
            then 1
            else fib (n P.- 1) P.+ fib (n P.- 2)

        fibRec :: Integer -> Integer
        fibRec = Rec.fix1zSimple $ \r n -> if n == 0 then 0 else if n == 1 then 1 else r (n-1) + r (n-2)

-- | Summing a list.
sumB :: Benchmark
sumB = bgroup "sum" [
        bgroup "5" [
            bench "plutus" $ nf unsafeEvaluateCek script5,
            bench "plutus-opt" $ nf unsafeEvaluateCek script5Opt,
            bench "native" $ nf haskellNative 5,
            bench "scott" $ nf haskellScott 5,
            bench "combinator" $ nf haskellRec 5,
            bench "scott-combinator" $ nf haskellRecScott 5
        ],
        bgroup "20" [
            bench "plutus" $ nf unsafeEvaluateCek script20,
            bench "plutus-opt" $ nf unsafeEvaluateCek script20Opt,
            bench "native" $ nf haskellNative 20,
            bench "scott" $ nf haskellScott 20,
            bench "combinator" $ nf haskellRec 20,
            bench "scott-combinator" $ nf haskellRecScott 20
        ]
    ]
    where
        fromTo :: Integer -> Integer -> [Integer]
        fromTo f t =
            if f P.== t then [f]
            else f:(fromTo (f P.+ 1) t)

        foldrRec :: (a -> b -> b) -> b -> [a] -> b
        foldrRec f z = go
            where go = Rec.fix1zSimple $ \r -> \case
                      [] -> z
                      (h:t) -> f h (r t)

        foldrScott :: (a -> b -> b) -> b -> Scott.ScottList a -> b
        foldrScott f z = go
            where go l = Scott.matchList l z (\h t -> f h (go t))

        foldrRecScott :: (a -> b -> b) -> b -> Scott.ScottList a -> b
        foldrRecScott f z = go
            where go = Rec.fix1zSimple $ \r l -> Scott.matchList l z (\h t -> f h (r t))

        haskellNative :: Integer -> Integer
        haskellNative i = foldr (+) 0 [1..i]

        haskellScott :: Integer -> Integer
        haskellScott i = foldrScott (+) 0 (Scott.fromTo 1 i)

        haskellRec :: Integer -> Integer
        haskellRec i = foldrRec (+) 0 [1..i]

        haskellRecScott :: Integer -> Integer
        haskellRecScott i = foldrRecScott (+) 0 (Scott.fromTo 1 i)

        script5 = PlutusTx.getPlc $$(PlutusTx.compile [|| P.foldr (P.+) 0 (fromTo 1 5) ||])
        script5Opt = PlutusTx.getPlc $$(PlutusTx.compile [|| foldrOpt (P.+) 0 (fromToOpt 1 5) ||])
        script20 = PlutusTx.getPlc $$(PlutusTx.compile [|| P.foldr (P.+) 0 (fromTo 1 20) ||])
        script20Opt = PlutusTx.getPlc $$(PlutusTx.compile [|| foldrOpt (P.+) 0 (fromToOpt 1 20) ||])

-- | This aims to exercise some reasonably substantial computation *without* using any builtins.
-- Hence we also provide explicitly constructed lists, rather than writing 'replicate', which would
-- require integers.
tailB :: Benchmark
tailB = bgroup "tail" [
        bgroup "5" [
            bench "plutus" $ nf unsafeEvaluateCek (PlutusTx.getPlc $$(PlutusTx.compile [|| \() () () -> tail [(), (), (), (), ()] ||])),
            bench "plutus-opt" $ nf unsafeEvaluateCek (PlutusTx.getPlc $$(PlutusTx.compile [|| \() () () -> tailOpt [(), (), (), (), ()] ||])),
            bench "native" $ nf tail (replicate 5 ()),
            bench "scott" $ nf tailScott (Scott.replicate 5 ()),
            bench "combinator" $ nf tailRec (replicate 5 ()),
            bench "scott-combinator" $ nf tailRecScott (Scott.replicate 5 ())
        ],
        bgroup "20" [
            bench "plutus" $ nf unsafeEvaluateCek (PlutusTx.getPlc $$(PlutusTx.compile [|| \() () () -> tail [(), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), ()] ||])),
            bench "plutus-opt" $ nf unsafeEvaluateCek (PlutusTx.getPlc $$(PlutusTx.compile [|| \() () () -> tailOpt [(), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), ()] ||])),
            bench "native" $ nf tail (replicate 20 ()),
            bench "scott" $ nf tailScott (Scott.replicate 20 ()),
            bench "combinator" $ nf tailRec (replicate 20 ()),
            bench "scott-combinator" $ nf tailRecScott (Scott.replicate 20 ())
        ]
    ]
    where
        tail :: [a] -> Maybe a
        tail = \case
            [] -> Nothing
            (x:[]) -> Just x
            (_:xs) -> tail xs

        tailRec :: [a] -> Maybe a
        tailRec = Rec.fix1zSimple $ \r -> \case
                [] -> Nothing
                (x:[]) -> Just x
                (_:xs) -> r xs

        tailScott :: Scott.ScottList a -> Maybe a
        tailScott l = Scott.matchList l Nothing (\h t -> Scott.matchList t (Just h) (\_h t' -> tailScott t'))

        tailRecScott :: Scott.ScottList a -> Maybe a
        tailRecScott = Rec.fix1zSimple $ \r l ->
            Scott.matchList l Nothing (\h t -> Scott.matchList t (Just h) (\_h t' -> r t'))

-- | Execution of some Plutus validators.
validators :: Benchmark
validators = bgroup "validators" [ trivial, multisig ]

-- | The trivial validator script that just returns 'True'.
trivial :: Benchmark
trivial = bgroup "trivial" [
        bench "nocheck" $ nf runScriptNoCheck (validationData1, validator, unitData, unitRedeemer),
        bench "typecheck" $ nf runScriptCheck (validationData1, validator, unitData, unitRedeemer)
    ]
    where
        validator = mkValidatorScript $$(PlutusTx.compile [|| \(_ :: PlutusTx.Data) (_ :: PlutusTx.Data) (_ :: PlutusTx.Data) -> () ||])

-- | The multisig contract is one of the simplest ones that we have. This runs a number of different scenarios.
-- Note that multisig also does some signature verification!
multisig :: Benchmark
multisig = bgroup "multisig" [
        bench "1of1" $ nf runScriptNoCheck
            (validationData2
            , MS.validator msScen1of1
            , unitData
            , unitRedeemer),
        bench "1of2" $ nf runScriptNoCheck
            (validationData2
            , MS.validator msScen1of2
            , unitData
            , unitRedeemer),
        bench "2of2" $ nf runScriptNoCheck
            (validationData2
            , MS.validator msScen2of2
            , unitData
            , unitRedeemer),
        bench "typecheck" $ nf runScriptCheck
            (validationData2
            , MS.validator msScen1of1
            , unitData
            , unitRedeemer)
    ]
    where
        msScen1of1 = MS.MultiSig { MS.signatories = [pk1], MS.minNumSignatures = 1 }
        msScen1of2 = MS.MultiSig { MS.signatories = [pk1, pk2], MS.minNumSignatures = 1 }
        msScen2of2 = MS.MultiSig { MS.signatories = [pk1, pk2], MS.minNumSignatures = 2 }

-- Test functions and data

verifySignature :: (PubKey, Digest SHA256, Signature) -> Bool
verifySignature (PubKey (LedgerBytes k), m, Signature s) = P.verifySignature k (BSL.fromStrict $ BA.convert m) s

runScriptNoCheck :: (ValidationData, Validator, DataValue, RedeemerValue) -> Either ScriptError [String]
runScriptNoCheck (vd, v, d, r) = runScript DontCheck vd v d r
runScriptCheck :: (ValidationData, Validator, DataValue, RedeemerValue) -> Either ScriptError [String]
runScriptCheck (vd, v, d, r) = runScript Typecheck vd v d r

privk1 :: PrivateKey
privk1 = Crypto.knownPrivateKeys !! 0
pk1 :: PubKey
pk1 = Crypto.toPublicKey privk1

privk2 :: PrivateKey
privk2 = Crypto.knownPrivateKeys !! 1
pk2 :: PubKey
pk2 = Crypto.toPublicKey privk2

txHash :: Digest SHA256
txHash = hash (""::BS.ByteString)

sig1 :: Signature
sig1 = Crypto.sign txHash privk1

sig2 :: Signature
sig2 = Crypto.sign txHash privk2

validationData1 :: ValidationData
validationData1 = ValidationData $ PlutusTx.toData $ mockPendingTx

validationData2 :: ValidationData
validationData2 = ValidationData $ PlutusTx.toData $ mockPendingTx { pendingTxSignatures = [(pk1, sig1), (pk2, sig2)] }

mockPendingTx :: PendingTx
mockPendingTx = PendingTx
    { pendingTxInputs = []
    , pendingTxOutputs = []
    , pendingTxFee = PlutusTx.zero
    , pendingTxForge = PlutusTx.zero
    , pendingTxIn = PendingTxIn
        { pendingTxInRef = PendingTxOutRef
            { pendingTxOutRefId = TxId P.emptyByteString
            , pendingTxOutRefIdx = 0
            }
        , pendingTxInWitness = (ValidatorHash "", RedeemerHash "", DataValueHash "")
        , pendingTxInValue = PlutusTx.zero
        }
    , pendingTxValidRange = defaultSlotRange
    , pendingTxSignatures = []
    , pendingTxId = TxId P.emptyByteString
    , pendingTxData = []
    }
