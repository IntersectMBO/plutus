{-# LANGUAGE TypeApplications #-}
module Evaluation.Builtins.Integer.Common
where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (builtin, mkIterAppNoAnn, mkTyBuiltin, tyInst)

import Evaluation.Builtins.Common

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

lessThanInteger :: PlcTerm -> PlcTerm -> PlcTerm
lessThanInteger a b = mkIterAppNoAnn (builtin () PLC.LessThanInteger) [a, b]

lessThanEqualsInteger :: PlcTerm -> PlcTerm -> PlcTerm
lessThanEqualsInteger a b = mkIterAppNoAnn (builtin () PLC.LessThanEqualsInteger) [a, b]

iteAtInteger :: PlcTerm -> PlcTerm -> PlcTerm -> PlcTerm
iteAtInteger b t f =
  let integerTy = mkTyBuiltin @_ @Integer ()
      ite = tyInst () (builtin () PLC.IfThenElse) integerTy
  in mkIterAppNoAnn ite [b, t, f]

abs :: PlcTerm -> PlcTerm
abs t = iteAtInteger (lessThanEqualsInteger zero t) t (subtractInteger zero t)

