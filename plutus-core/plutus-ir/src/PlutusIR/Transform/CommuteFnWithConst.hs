{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}

module PlutusIR.Transform.CommuteFnWithConst (commuteFnWithConst) where

import Data.Typeable (Typeable, eqT)
import PlutusCore.Default
import PlutusIR.Core (Term (Apply, Builtin, Constant))

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

isConstant :: Term tyname name uni fun a -> Bool
isConstant Constant{} = True
isConstant _          = False

commuteFnWithConstDefault ::
    forall tyname name uni a.
    Term tyname name uni DefaultFun a ->
    Term tyname name uni DefaultFun a
commuteFnWithConstDefault tm@(Apply ann (Apply ann1 (Builtin annB fun) x) y) =
  case (isCommutativeWithConstant fun, isConstant x, isConstant y) of
    (True, False, True) -> Apply ann (Apply ann1 (Builtin annB fun) y) x
    _                   -> tm
commuteFnWithConstDefault tm = tm

commuteFnWithConst :: forall tyname name uni fun a. Typeable fun =>
    Term tyname name uni fun a -> Term tyname name uni fun a
commuteFnWithConst = case eqT @fun @DefaultFun of
    Just Refl -> commuteFnWithConstDefault
    Nothing   -> id

-- | Returns whether a `DefaultFun` is commutative with `Constant`'s as arguments. Not using
-- catchall to make sure that this function catches newly added `DefaultFun`.
isCommutativeWithConstant :: DefaultFun -> Bool
isCommutativeWithConstant = \case
  AddInteger                      -> False
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
  Blake2b_256                     -> False
  VerifyEd25519Signature          -> False
  VerifyEcdsaSecp256k1Signature   -> False
  VerifySchnorrSecp256k1Signature -> False
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
  EqualsData                      -> False -- doesn't take constant
  SerialiseData                   -> False
  MkPairData                      -> False
  MkNilData                       -> False
  MkNilPairData                   -> False
