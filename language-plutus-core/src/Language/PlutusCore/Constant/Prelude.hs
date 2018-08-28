{-# LANGUAGE QuasiQuotes #-}

module Language.PlutusCore.Constant.Prelude
    ( Size
    , Value
    , getBuiltinUnit
    , getBuiltinUnitval
    , getBuiltinBool
    , getBuiltinTrue
    , getBuiltinFalse
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.TH
import           Language.PlutusCore.Type
import           PlutusPrelude

type Size = Natural
type Value = Term

-- | Church-encoded '()' as a PLC type.
--
-- > all (A :: *). A -> A
getBuiltinUnit :: Quote (Type TyName ())
getBuiltinUnit = [plcType|(all a (type) (fun a a))|]

-- | Church-encoded '()' as a PLC term.
--
-- > /\(A :: *) -> \(x : A) -> x
getBuiltinUnitval :: Quote (Value TyName Name ())
getBuiltinUnitval = [plcTerm|(abs a (type) (lam x a x))|]

-- | Church-encoded '()' as a PLC type.
--
-- > all (A :: *). (() -> A) -> (() -> A) -> A
getBuiltinBool :: Quote (Type TyName ())
getBuiltinBool = [plcType|(all a (type)
                         (fun
                         (fun getBuiltinUnit a)
                         (fun
                         (fun getBuiltinUnit a)
                         a)))|]

-- | Church-encoded 'True' as a PLC term.
--
-- > /\(A :: *) -> \(x y : () -> A) -> x ()
getBuiltinTrue :: Quote (Value TyName Name ())
getBuiltinTrue = [plcTerm|(abs a (type)
                         (lam x (fun getBuiltinUnit a)
                         (lam y (fun getBuiltinUnit a)
                         [x getBuiltinUnitval])))|]

-- | Church-encoded 'False' as a PLC term.
--
-- > /\(A :: *) -> \(x y : () -> A) -> y ()
getBuiltinFalse :: Quote (Value TyName Name ())
getBuiltinFalse = [plcTerm|(abs a (type)
                         (lam x (fun getBuiltinUnit a)
                         (lam y (fun getBuiltinUnit a)
                         [y getBuiltinUnitval])))|]
