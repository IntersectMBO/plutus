{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Evaluation.Builtins.Integer.Common
where

import Prelude hiding (and, not, or)

import PlutusCore qualified as PLC
import PlutusCore.Generators.QuickCheck.Builtin (AsArbitraryBuiltin (..))
import PlutusCore.MkPlc (builtin, mkIterAppNoAnn, mkTyBuiltin, tyInst)

import Evaluation.Builtins.Common

import Test.QuickCheck (Arbitrary, Gen, arbitrary, choose, oneof)

{- We don't want to use the standard QuickCheck generator for Integers in these
   property tests because that only produces values in [-99..99].  Instead we
   mix the better generator for AsArbitraryBuiltin Integer and one which
   produces Integers up to 400 bits.  The name `BigInteger` is maybe slightly
   misleading but it has the merit of being relatively short.
-}
arbitraryBigInteger :: Gen Integer
arbitraryBigInteger =
  oneof
    [ unAsArbitraryBuiltin <$> arbitrary
    , choose (-b, b)
    ]
  where
    b = (2 :: Integer) ^ (400 :: Integer)

newtype BigInteger = BigInteger Integer
  deriving newtype (Show, Eq, Ord, Num)

instance Arbitrary BigInteger where
  arbitrary = BigInteger <$> arbitraryBigInteger

biginteger :: BigInteger -> PlcTerm
biginteger (BigInteger n) = integer n

-- Functions creating terms that are applications of various builtins, for
-- convenience.

addInteger :: PlcTerm -> PlcTerm -> PlcTerm
addInteger a b = mkIterAppNoAnn (builtin () PLC.AddInteger) [a, b]

subtractInteger :: PlcTerm -> PlcTerm -> PlcTerm
subtractInteger a b = mkIterAppNoAnn (builtin () PLC.SubtractInteger) [a, b]

divideInteger :: PlcTerm -> PlcTerm -> PlcTerm
divideInteger a b = mkIterAppNoAnn (builtin () PLC.DivideInteger) [a, b]

modInteger :: PlcTerm -> PlcTerm -> PlcTerm
modInteger a b = mkIterAppNoAnn (builtin () PLC.ModInteger) [a, b]

multiplyInteger :: PlcTerm -> PlcTerm -> PlcTerm
multiplyInteger a b = mkIterAppNoAnn (builtin () PLC.MultiplyInteger) [a, b]

quotientInteger :: PlcTerm -> PlcTerm -> PlcTerm
quotientInteger a b = mkIterAppNoAnn (builtin () PLC.QuotientInteger) [a, b]

remainderInteger :: PlcTerm -> PlcTerm -> PlcTerm
remainderInteger a b = mkIterAppNoAnn (builtin () PLC.RemainderInteger) [a, b]

equalsInteger :: PlcTerm -> PlcTerm -> PlcTerm
equalsInteger a b = mkIterAppNoAnn (builtin () PLC.EqualsInteger) [a, b]

lessThanInteger :: PlcTerm -> PlcTerm -> PlcTerm
lessThanInteger a b = mkIterAppNoAnn (builtin () PLC.LessThanInteger) [a, b]

lessThanEqualsInteger :: PlcTerm -> PlcTerm -> PlcTerm
lessThanEqualsInteger a b = mkIterAppNoAnn (builtin () PLC.LessThanEqualsInteger) [a, b]

le0 :: PlcTerm -> PlcTerm
le0 t = lessThanEqualsInteger t zero

ge0 :: PlcTerm -> PlcTerm
ge0 t = lessThanEqualsInteger zero t

ite
  :: forall a
   . PLC.DefaultUni `PLC.HasTypeLevel` a
  => PlcTerm -> PlcTerm -> PlcTerm -> PlcTerm
ite b t f =
  let ty = mkTyBuiltin @_ @a ()
      iteInst = tyInst () (builtin () PLC.IfThenElse) ty
   in mkIterAppNoAnn iteInst [b, t, f]

-- Various logical combinations of boolean terms.

abs :: PlcTerm -> PlcTerm
abs t = ite @Integer (lessThanEqualsInteger zero t) t (subtractInteger zero t)

not :: PlcTerm -> PlcTerm
not t = ite @Bool t false true

and :: PlcTerm -> PlcTerm -> PlcTerm
and t1 t2 = ite @Bool t1 (ite @Bool t2 true false) false

or :: PlcTerm -> PlcTerm -> PlcTerm
or t1 t2 = ite @Bool t1 true (ite @Bool t2 true false)

xor :: PlcTerm -> PlcTerm -> PlcTerm
xor t1 t2 = ite @Bool t1 (ite @Bool t2 false true) t2

implies :: PlcTerm -> PlcTerm -> PlcTerm
implies t1 t2 = (not t1) `or` t2

iff :: PlcTerm -> PlcTerm -> PlcTerm
iff t1 t2 = (t1 `implies` t2) `and` (t2 `implies` t1)
