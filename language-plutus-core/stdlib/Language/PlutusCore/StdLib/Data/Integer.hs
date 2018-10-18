-- | Functions related to @integer@.

{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.StdLib.Data.Integer
    ( getBuiltinSuccInteger
    ) where

import           Language.PlutusCore.Constant (makeDynamicBuiltinInt)
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

-- |  @succ :: Integer -> Integer@ as a PLC term.
--
-- > /\(s :: size) -> \(ss : size s) (i : integer s) ->
-- >     addInteger {s} i (resizeInteger {1} {s} ss 1!1)
getBuiltinSuccInteger :: Quote (Term TyName Name ())
getBuiltinSuccInteger = do
    s <- freshTyName () "s"
    ss <- freshName () "ss"
    i  <- freshName () "i"
    return
        . TyAbs () s (Size ())
        . LamAbs () ss (TyApp () (TyBuiltin () TySize) $ TyVar () s)
        . LamAbs () i (TyApp () (TyBuiltin () TyInteger) $ TyVar () s)
        . mkIterApp (TyInst () (Constant () $ BuiltinName () AddInteger) $ TyVar () s)
        $ [ Var () i
          , makeDynamicBuiltinInt (TyVar () s) (Var () ss) 1
          ]
