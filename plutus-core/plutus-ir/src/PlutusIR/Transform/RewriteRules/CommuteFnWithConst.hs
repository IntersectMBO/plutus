{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}

{-| Commute such that constants are the first arguments. Consider:

(1)    equalsInteger 1 x

(2)    equalsInteger x 1

We have unary application, so these are two partial applications:

(1)    (equalsInteger 1) x

(2)    (equalsInteger x) 1

With (1), we can share the `equalsInteger 1` node, and it will be the same across any place where
we do this.

With (2), both the nodes here include x, which is a variable that will likely be different in other
invocations of `equalsInteger`. So the second one is harder to share, which is worse for CSE.

So commuting `equalsInteger` so that it has the constant first both a) makes various occurrences of
`equalsInteger` more likely to look similar, and b) gives us a maximally-shareable node for CSE.

This applies to any commutative builtin function that takes constants as arguments, although we
might expect that `equalsInteger` is the one that will benefit the most.
Plutonomy only commutes `EqualsInteger` in their `commEquals`. -}
module PlutusIR.Transform.RewriteRules.CommuteFnWithConst
  ( commuteFnWithConst
  ) where

import PlutusCore.Default
import PlutusIR.Core.Type (Term (Apply, Builtin, Constant))

isConstant :: Term tyname name uni fun a -> Bool
isConstant = \case
  Constant {} -> True
  _ -> False

commuteFnWithConst :: t ~ Term tyname name uni DefaultFun a => t -> t
commuteFnWithConst = \case
  Apply ann1 (Apply ann2 (Builtin ann3 fun) arg1) arg2
    | isCommutative fun
    , not (isConstant arg1)
    , isConstant arg2 ->
        Apply ann1 (Apply ann2 (Builtin ann3 fun) arg2) arg1
  t -> t

{-| Returns whether a `DefaultFun` is commutative. Not using
catchall to make sure that this function catches newly added `DefaultFun`. -}
isCommutative :: DefaultFun -> Bool
isCommutative = \case
  AddInteger -> True
  MultiplyInteger -> True
  EqualsInteger -> True
  EqualsByteString -> True
  EqualsString -> True
  EqualsData -> True
  -- verbose laid down, to revisit this function if a new builtin is added
  SubtractInteger -> False
  DivideInteger -> False
  QuotientInteger -> False
  RemainderInteger -> False
  ModInteger -> False
  LessThanInteger -> False
  LessThanEqualsInteger -> False
  AppendByteString -> False
  ConsByteString -> False
  SliceByteString -> False
  LengthOfByteString -> False
  IndexByteString -> False
  LessThanByteString -> False
  LessThanEqualsByteString -> False
  Sha2_256 -> False
  Sha3_256 -> False
  Blake2b_224 -> False
  Blake2b_256 -> False
  Keccak_256 -> False
  Ripemd_160 -> False
  VerifyEd25519Signature -> False
  VerifyEcdsaSecp256k1Signature -> False
  VerifySchnorrSecp256k1Signature -> False
  Bls12_381_G1_add -> False
  Bls12_381_G1_neg -> False
  Bls12_381_G1_scalarMul -> False
  Bls12_381_G1_multiScalarMul -> False
  Bls12_381_G1_equal -> False
  Bls12_381_G1_hashToGroup -> False
  Bls12_381_G1_compress -> False
  Bls12_381_G1_uncompress -> False
  Bls12_381_G2_add -> False
  Bls12_381_G2_neg -> False
  Bls12_381_G2_scalarMul -> False
  Bls12_381_G2_multiScalarMul -> False
  Bls12_381_G2_equal -> False
  Bls12_381_G2_hashToGroup -> False
  Bls12_381_G2_compress -> False
  Bls12_381_G2_uncompress -> False
  Bls12_381_millerLoop -> False
  Bls12_381_mulMlResult -> False
  Bls12_381_finalVerify -> False
  AppendString -> False
  EncodeUtf8 -> False
  DecodeUtf8 -> False
  IfThenElse -> False
  ChooseUnit -> False
  Trace -> False
  FstPair -> False
  SndPair -> False
  ChooseList -> False
  MkCons -> False
  HeadList -> False
  TailList -> False
  NullList -> False
  LengthOfArray -> False
  ListToArray -> False
  IndexArray -> False
  ChooseData -> False
  ConstrData -> False
  MapData -> False
  ListData -> False
  IData -> False
  BData -> False
  UnConstrData -> False
  UnMapData -> False
  UnListData -> False
  UnIData -> False
  UnBData -> False
  SerialiseData -> False
  MkPairData -> False
  MkNilData -> False
  MkNilPairData -> False
  IntegerToByteString -> False
  ByteStringToInteger -> False
  -- Currently, this requires commutativity in all arguments, which the
  -- logical and bitwise operations are not.
  AndByteString -> False
  OrByteString -> False
  XorByteString -> False
  ComplementByteString -> False
  ReadBit -> False
  WriteBits -> False
  ReplicateByte -> False
  ShiftByteString -> False
  RotateByteString -> False
  CountSetBits -> False
  FindFirstSetBit -> False
  ExpModInteger -> False
  DropList -> False
  InsertCoin -> False
  LookupCoin -> False
  UnionValue -> True
  ValueContains -> False
  ValueData -> False
  UnValueData -> False
  ScaleValue -> False
