{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds         #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module Main (main) where

import           Prelude                                           hiding (tail)

import           Control.Lens.Indexed
import           Criterion.Main
import           Crypto.Hash
import qualified Data.ByteString                                   as BS
import qualified Language.PlutusTx.Coordination.Contracts.MultiSig as MS
import qualified Language.PlutusTx.Prelude                         as P
import           Ledger
import           Ledger.Ada                                        as Ada
import qualified Ledger.Crypto                                     as Crypto
import           Ledger.Value                                      as Value
import           LedgerBytes
import           Wallet

main :: IO ()
main = defaultMain [ expensive, plutus ]

-- | Execution of some expensive operations that we can relevantly compare ourselves against.
expensive :: Benchmark
expensive = bgroup "expensive" [ verifySignatureB, hashB ]

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

-- | Execution of some Plutus programs.
plutus :: Benchmark
plutus = bgroup "plutus" [ trivial, fibB, sumB, tailB, multisig ]

-- | The trivial validator script that just returns 'True'.
trivial :: Benchmark
trivial = bgroup "trivial" [
        bench "nocheck" $ nf runScriptNoCheck (validationData1, validator, unitData, unitRedeemer),
        bench "typecheck" $ nf runScriptCheck (validationData1, validator, unitData, unitRedeemer)
    ]
    where
        validator = ValidatorScript $$(Ledger.compileScript [|| \() () (_::PendingTx) -> True ||])

-- | The fibonnaci function.
fibB :: Benchmark
fibB = bgroup "fib" [
        bench "5" $ nf runScriptNoCheck (validationData1, validator5, unitData, unitRedeemer),
        bench "10" $ nf runScriptNoCheck (validationData1, validator10, unitData, unitRedeemer),
        bench "typecheck" $ nf runScriptCheck (validationData1, validator5, unitData, unitRedeemer)
    ]
    where
        fib :: Integer -> Integer
        fib n =
            if n P.== 0
            then 0
            else if n P.== 1
            then 1
            else fib (n `P.minus` 1) `P.plus` fib (n `P.minus` 2)
        validator5 = ValidatorScript $$(Ledger.compileScript
                                         [|| \() () (_::PendingTx) -> fib 5 P.== 5 ||])
        validator10 = ValidatorScript $$(Ledger.compileScript
                                         [|| \() () (_::PendingTx) -> fib 10 P.== 55 ||])

-- | Summing a list.
sumB :: Benchmark
sumB = bgroup "sum" [
        bench "5" $ nf runScriptNoCheck (validationData1, validator5, unitData, unitRedeemer),
        bench "20" $ nf runScriptNoCheck (validationData1, validator20, unitData, unitRedeemer),
        bench "typecheck" $ nf runScriptCheck (validationData1, validator5, unitData, unitRedeemer)
    ]
    where
        fromTo :: Integer -> Integer -> [Integer]
        fromTo f t =
            if f P.== t then [f]
            else f:(fromTo (f `P.plus` 1) t)

        validator5 = ValidatorScript $$(Ledger.compileScript
                                         [|| \() () (_::PendingTx) -> P.foldr P.plus 0 (fromTo 1 5) P.== 15 ||])
        validator20 = ValidatorScript $$(Ledger.compileScript
                                         [|| \() () (_::PendingTx) -> P.foldr P.plus 0 (fromTo 1 20) P.== 210 ||])

-- | This aims to exercise some reasonably substantial computation *without* using any builtins.
-- Hence we also provide explicitly constructed lists, rather than writing 'replicate', which would
-- require integers.
tailB :: Benchmark
tailB = bgroup "tail" [
        bench "5" $ nf runScriptNoCheck (validationData1, validator5, unitData, unitRedeemer),
        bench "20" $ nf runScriptNoCheck (validationData1, validator20, unitData, unitRedeemer),
        bench "typecheck" $ nf runScriptCheck (validationData1, validator5, unitData, unitRedeemer)
    ]
    where
        tail :: [a] -> Maybe a
        tail [] = Nothing
        tail (x:[]) = Just x
        tail (_:xs) = tail xs

        validator5 = ValidatorScript $$(Ledger.compileScript
                                         [|| \() () (_::PendingTx) -> tail [(), (), (), (), ()] P.== Just () ||])
        validator20 = ValidatorScript $$(Ledger.compileScript
                                         [|| \() () (_::PendingTx) -> tail [(), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), (), ()] P.== Just () ||])

-- | The multisig contract is one of the simplest ones that we have. This runs a number of different scenarios.
-- Note that multisig also does some signature verification!
multisig :: Benchmark
multisig = bgroup "multisig" [
        bench "1of1" $ nf runScriptNoCheck
            (validationData2
            , MS.msValidator msScen1of1
            , MS.msDataScript
            , MS.msRedeemer),
        bench "1of2" $ nf runScriptNoCheck
            (validationData2
            , MS.msValidator msScen1of2
            , MS.msDataScript
            , MS.msRedeemer),
        bench "2of2" $ nf runScriptNoCheck
            (validationData2
            , MS.msValidator msScen2of2
            , MS.msDataScript
            , MS.msRedeemer),
        bench "typecheck" $ nf runScriptCheck
            (validationData2
            , MS.msValidator msScen1of1
            , MS.msDataScript
            , MS.msRedeemer)
    ]
    where
        msScen1of1 = MS.MultiSig { MS.signatories = [pk1], MS.requiredSignatures = 1 }
        msScen1of2 = MS.MultiSig { MS.signatories = [pk1, pk2], MS.requiredSignatures = 1 }
        msScen2of2 = MS.MultiSig { MS.signatories = [pk1, pk2], MS.requiredSignatures = 2 }

-- Test functions and data

verifySignature :: (PubKey, Digest SHA256, Signature) -> Bool
verifySignature (PubKey (LedgerBytes k), m, Signature s) = P.verifySignature k (plcDigest m) s

runScriptNoCheck :: (ValidationData, ValidatorScript, DataScript, RedeemerScript) -> ([String], Bool)
runScriptNoCheck (vd, v, d, r) = runScript DontCheck vd v d r
runScriptCheck :: (ValidationData, ValidatorScript, DataScript, RedeemerScript) -> ([String], Bool)
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
validationData1 = ValidationData $ lifted $ mockPendingTx

validationData2 :: ValidationData
validationData2 = ValidationData $ lifted $ mockPendingTx { pendingTxSignatures = [(pk1, sig1), (pk2, sig2)] }

mockPendingTx :: PendingTx
mockPendingTx = PendingTx
    { pendingTxInputs = []
    , pendingTxOutputs = []
    , pendingTxFee = Ada.zero
    , pendingTxForge = Value.zero
    , pendingTxIn = PendingTxIn
        { pendingTxInRef = PendingTxOutRef
            { pendingTxOutRefId = TxHash P.emptyByteString
            , pendingTxOutRefIdx = 0
            }
        , pendingTxInWitness = Nothing
        , pendingTxInValue = Value.zero
        }
    , pendingTxValidRange = defaultSlotRange
    , pendingTxSignatures = []
    , pendingTxHash = TxHash P.emptyByteString
    }
