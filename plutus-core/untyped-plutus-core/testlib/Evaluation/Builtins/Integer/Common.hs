{-# LANGUAGE TypeApplications #-}
module Evaluation.Builtins.Integer.Common
where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (builtin, mkIterAppNoAnn, mkTyBuiltin, tyInst)

import Evaluation.Builtins.Common

import Prelude hiding (and, not, or)

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

iteAt :: PlcType -> PlcTerm -> PlcTerm -> PlcTerm -> PlcTerm
iteAt ty b t f =
  let ite = tyInst () (builtin () PLC.IfThenElse) ty
  in mkIterAppNoAnn ite [b, t, f]

iteAtInteger :: PlcTerm -> PlcTerm -> PlcTerm -> PlcTerm
iteAtInteger = iteAt (mkTyBuiltin @_ @Integer ())

iteAtBool :: PlcTerm -> PlcTerm -> PlcTerm -> PlcTerm
iteAtBool = iteAt (mkTyBuiltin @_ @Bool ())

abs :: PlcTerm -> PlcTerm
abs t = iteAtInteger (lessThanEqualsInteger zero t) t (subtractInteger zero t)

not :: PlcTerm -> PlcTerm
not t = iteAtBool t false true

and :: PlcTerm -> PlcTerm -> PlcTerm
and t1 t2 = iteAtBool t1 (iteAtBool t2 true false) false

or :: PlcTerm -> PlcTerm -> PlcTerm
or t1 t2 = iteAtBool t1 true (iteAtBool t2 true false)

xor :: PlcTerm -> PlcTerm -> PlcTerm
xor t1 t2 = iteAtBool t1 (iteAtBool t2 false true) t2

implies :: PlcTerm -> PlcTerm -> PlcTerm
implies t1 t2 = (not t1) `or` t2

iff :: PlcTerm -> PlcTerm -> PlcTerm
iff t1 t2 = (t1 `implies` t2) `and` (t2 `implies` t1)
