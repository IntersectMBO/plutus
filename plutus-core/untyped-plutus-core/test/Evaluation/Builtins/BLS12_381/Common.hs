module Evaluation.Builtins.BLS12_381.Common
where

import PlutusCore.BLS12_381.G1 qualified as G1
import PlutusCore.BLS12_381.G2 qualified as G2

import Data.ByteString as BS (ByteString, pack)
import UntypedPlutusCore as UPLC

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

import Evaluation.Builtins.Common
import PlutusCore as PLC
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults

import PlutusCore.MkPlc (builtin, mkConstant, mkIterApp)


-- Hedgehog stuff

withNTests :: Property -> Property
withNTests = withTests 500

genByteString100 :: Gen ByteString
genByteString100 = Gen.bytes $ Range.linear 0 100

genByteString :: Gen ByteString
genByteString = Gen.bytes $ Range.linear 0 1000

genG1element :: Gen G1.Element
genG1element = G1.hashToCurve <$> Gen.bytes (Range.linear 0 64)

genG2element :: Gen G2.Element
genG2element = G2.hashToCurve <$> Gen.bytes (Range.linear 0 64)

genSmallScalar :: Gen Integer
genSmallScalar = Gen.integral $ Range.linear (-100) 100

genScalar :: Gen Integer
genScalar = Gen.integral $ Range.linear (-10000) 10000

-- PLC utilities

type PlcTerm = PLC.Term TyName Name DefaultUni DefaultFun ()
type UplcTerm = UPLC.Term Name DefaultUni DefaultFun ()

uplcTrue :: Maybe UplcTerm
uplcTrue = Just $ mkConstant () True

uplcFalse :: Maybe UplcTerm
uplcFalse = Just $ mkConstant () False

integer :: Integer -> PlcTerm
integer = mkConstant ()

bytestring :: ByteString -> PlcTerm
bytestring = mkConstant ()

g1elt :: G1.Element ->  PlcTerm
g1elt = mkConstant ()

g2elt :: G2.Element ->  PlcTerm
g2elt = mkConstant ()

mkApp1 :: DefaultFun -> PlcTerm -> PlcTerm
mkApp1 b x = mkIterApp () (builtin () b) [x]

mkApp2 :: DefaultFun -> PlcTerm -> PlcTerm -> PlcTerm
mkApp2 b x y = mkIterApp () (builtin () b) [x,y]

-- Constructing G1 builtin application terms

addG1 :: PlcTerm -> PlcTerm -> PlcTerm
addG1 = mkApp2 Bls12_381_G1_add

eqG1 :: PlcTerm -> PlcTerm -> PlcTerm
eqG1 = mkApp2 Bls12_381_G1_equal

mulG1 :: PlcTerm -> PlcTerm -> PlcTerm
mulG1 = mkApp2 Bls12_381_G1_mul


negG1 :: PlcTerm -> PlcTerm
negG1 = mkApp1 Bls12_381_G1_neg

uncompressG1 :: PlcTerm -> PlcTerm
uncompressG1 = mkApp1 Bls12_381_G1_uncompress

compressG1 :: PlcTerm -> PlcTerm
compressG1 = mkApp1 Bls12_381_G1_compress

hashToCurveG1 :: PlcTerm -> PlcTerm
hashToCurveG1 = mkApp1 Bls12_381_G1_hashToCurve

zeroG1 :: PlcTerm
zeroG1 =
    let b = bytestring $ pack (0xc0 : replicate 47 0x00)
    in uncompressG1 b

-- Constructing G2 builtin application terms

addG2 :: PlcTerm -> PlcTerm -> PlcTerm
addG2 = mkApp2 Bls12_381_G2_add

eqG2 :: PlcTerm -> PlcTerm -> PlcTerm
eqG2 = mkApp2 Bls12_381_G2_equal

mulG2 :: PlcTerm -> PlcTerm -> PlcTerm
mulG2 = mkApp2 Bls12_381_G2_mul


negG2 :: PlcTerm -> PlcTerm
negG2 = mkApp1 Bls12_381_G2_neg

uncompressG2 :: PlcTerm -> PlcTerm
uncompressG2 = mkApp1 Bls12_381_G2_uncompress

compressG2 :: PlcTerm -> PlcTerm
compressG2 = mkApp1 Bls12_381_G2_compress

hashToCurveG2 :: PlcTerm -> PlcTerm
hashToCurveG2 = mkApp1 Bls12_381_G2_hashToCurve

zeroG2 :: PlcTerm
zeroG2 =
    let b = bytestring $ pack (0xc0 : replicate 95 0x00)
    in uncompressG2 b

-- Constructing pairing terms

pairingPlc :: PlcTerm -> PlcTerm -> PlcTerm
pairingPlc = mkApp2 Bls12_381_GT_pairing

finalVerifyPlc :: PlcTerm -> PlcTerm -> PlcTerm
finalVerifyPlc = mkApp2 Bls12_381_GT_finalVerify

mulGT :: PlcTerm -> PlcTerm -> PlcTerm
mulGT = mkApp2 Bls12_381_GT_mul

-- Evaluating PLC terms

evalTerm
    :: PLC.Term TyName Name DefaultUni DefaultFun ()
    -> Maybe (UPLC.Term Name DefaultUni DefaultFun ())
evalTerm term =
    case typecheckEvaluateCekNoEmit DefaultFunV1 defaultBuiltinCostModel term
    of Left _ -> Nothing
       Right x  ->
           case x of
             EvaluationFailure   -> Nothing
             EvaluationSuccess s -> Just s

