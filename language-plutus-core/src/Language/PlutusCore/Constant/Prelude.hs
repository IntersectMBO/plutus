{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}

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
import           Language.PlutusCore.Type
import           PlutusPrelude
import           Language.PlutusCore.Quote
import           Language.PlutusCore.TH

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
getBuiltinBool = do
    unit <- getBuiltinUnit
    [plcType|(all a (type)
              (fun
              (fun unit a)
              (fun
              (fun unit a)
              a)))|]

-- | Church-encoded 'True' as a PLC term.
--
-- > /\(A :: *) -> \(x y : () -> A) -> x ()
getBuiltinTrue :: Quote (Value TyName Name ())
getBuiltinTrue = do
    unit <- getBuiltinUnit
    unitval <- getBuiltinUnitval
    [plcTerm|(abs a (type)
              (lam x (fun unit a)
              (lam y (fun unit a)
              [x unitval])))|]

-- | Church-encoded 'False' as a PLC term.
--
-- > /\(A :: *) -> \(x y : () -> A) -> y ()
getBuiltinFalse :: Quote (Value TyName Name ())
getBuiltinFalse = do
    unit <- getBuiltinUnit
    unitval <- getBuiltinUnitval
    [plcTerm|(abs a (type)
              (lam x (fun unit a)
              (lam y (fun unit a)
              [y unitval])))|]
