{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}

{- | Commute such that constants are the first arguments. Consider:

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
Plutonomy only commutes `EqualsInteger` in their `commEquals`.
-}

module PlutusIR.Transform.CommuteFnWithConst
  (commuteFnWithConst
  , commuteDefaultFun)
  where

import Control.Lens (over)
import Data.Typeable (Typeable, eqT)
import PlutusCore.Default
import PlutusIR.Core.Plated (termSubterms)
import PlutusIR.Core.Type (Term (Apply, Builtin, Constant))

isConstant :: Term tyname name uni fun a -> Bool
isConstant Constant{} = True
isConstant _          = False

commuteDefaultFun ::
    forall tyname name uni a.
    Term tyname name uni DefaultFun a ->
    Term tyname name uni DefaultFun a
commuteDefaultFun = over termSubterms commuteDefaultFun . localCommute
  where
    localCommute tm@(Apply ann (Apply ann1 (Builtin annB fun) x) y@Constant{})
      | isCommutative fun && not (isConstant x) =
          Apply ann (Apply ann1 (Builtin annB fun) y) x
      | otherwise                   = tm
    localCommute tm = tm

commuteFnWithConst :: forall tyname name uni fun a. Typeable fun =>
    Term tyname name uni fun a -> Term tyname name uni fun a
commuteFnWithConst = case eqT @fun @DefaultFun of
    Just Refl -> commuteDefaultFun
    Nothing   -> id

-- | Returns whether a `DefaultFun` is commutative. Not using
-- catchall to make sure that this function catches newly added `DefaultFun`.
isCommutative :: DefaultFun -> Bool
isCommutative = \case
  AddInteger                      -> True
  SubtractInteger                 -> False
  MultiplyInteger                 -> True
  DivideInteger                   -> False
  QuotientInteger                 -> False
  RemainderInteger                -> False
  ModInteger                      -> False
  EqualsInteger                   -> True
  LessThanInteger                 -> False
  LessThanEqualsInteger           -> False
    -- Bytestrings
  AppendByteString                -> False
  ConsByteString                  -> False
  SliceByteString                 -> False
  LengthOfByteString              -> False
  IndexByteString                 -> False
  EqualsByteString                -> True
  LessThanByteString              -> False
  LessThanEqualsByteString        -> False
    -- Cryptography and hashes
  Sha2_256                        -> False
  Sha3_256                        -> False
  Blake2b_224                     -> False
  Blake2b_256                     -> False
  Keccak_256                      -> False
  VerifyEd25519Signature          -> False
  VerifyEcdsaSecp256k1Signature   -> False
  VerifySchnorrSecp256k1Signature -> False
  Bls12_381_G1_add                -> False
  Bls12_381_G1_neg                -> False
  Bls12_381_G1_scalarMul          -> False
  Bls12_381_G1_equal              -> False
  Bls12_381_G1_hashToGroup        -> False
  Bls12_381_G1_compress           -> False
  Bls12_381_G1_uncompress         -> False
  Bls12_381_G2_add                -> False
  Bls12_381_G2_neg                -> False
  Bls12_381_G2_scalarMul          -> False
  Bls12_381_G2_equal              -> False
  Bls12_381_G2_hashToGroup        -> False
  Bls12_381_G2_compress           -> False
  Bls12_381_G2_uncompress         -> False
  Bls12_381_millerLoop            -> False
  Bls12_381_mulMlResult           -> False
  Bls12_381_finalVerify           -> False
    -- Strings
  AppendString                    -> False
  EqualsString                    -> True
  EncodeUtf8                      -> False
  DecodeUtf8                      -> False
    -- Bool
  IfThenElse                      -> False
    -- Unit
  ChooseUnit                      -> False
    -- Tracing
  Trace                           -> False
    -- Pairs
  FstPair                         -> False
  SndPair                         -> False
    -- Lists
  ChooseList                      -> False
  MkCons                          -> False
  HeadList                        -> False
  TailList                        -> False
  NullList                        -> False
    -- Data
  ChooseData                      -> False
  ConstrData                      -> False
  MapData                         -> False
  ListData                        -> False
  IData                           -> False
  BData                           -> False
  UnConstrData                    -> False
  UnMapData                       -> False
  UnListData                      -> False
  UnIData                         -> False
  UnBData                         -> False
  EqualsData                      -> True
  SerialiseData                   -> False
  MkPairData                      -> False
  MkNilData                       -> False
  MkNilPairData                   -> False
