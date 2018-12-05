-- | Functions that generate Plutus Core terms from Haskell values and vice versa.

{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.StdLib.Meta
    ( getBuiltinIntegerToNat
    , getBuiltinNatSum
    , getListToBuiltinList
    ) where

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Type
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | Convert an 'Integer' to a @nat@. TODO: convert PLC's @integer@ to @nat@ instead.
getBuiltinIntegerToNat :: Integer -> Quote (Term TyName Name ())
getBuiltinIntegerToNat n
    | n < 0     = error $ "getBuiltinIntegerToNat: negative argument: " ++ show n
    | otherwise = go n where
          go 0 = getBuiltinZero
          go m = Apply () <$> getBuiltinSucc <*> go (m - 1)

-- | @sumNat@ as a PLC term.
getBuiltinNatSum :: Natural -> Quote (Term TyName Name ())
getBuiltinNatSum s = rename =<< do
    foldList <- getBuiltinFoldList
    let int = TyApp () (TyBuiltin () TyInteger) $ TyInt () s
    let add = TyInst () (Builtin () (BuiltinName () AddInteger)) $ TyInt () s
    RecursiveType _ nat1 <- holedToRecursive <$> getBuiltinNat
    nti <- getBuiltinNatToInteger
    acc <- freshName () "acc"
    n <- freshName () "n"
    RecursiveType _ nat2 <- holedToRecursive <$> getBuiltinNat
    return
        $ mkIterApp () (mkIterInst () foldList [nat1, int])
          [   LamAbs () acc int
            . LamAbs () n nat2
            . mkIterApp () add
            $ [ Var () acc
              , mkIterApp () (TyInst () nti (TyInt () s))
                  [ Constant () $ BuiltinSize () s
                  , Var () n
                  ]
              ]
          , Constant () $ BuiltinInt () s 0
          ]

-- | Convert a Haskell list of 'Term's to a PLC @list@.
getListToBuiltinList :: Type TyName () -> [Term TyName Name ()] -> Quote (Term TyName Name ())
getListToBuiltinList ty ts = rename =<< do
    builtinNil  <- getBuiltinNil
    builtinCons <- getBuiltinCons
    return $ foldr
        (\x xs -> foldl' (Apply ()) (TyInst () builtinCons ty) [x, xs])
        (TyInst () builtinNil ty)
        ts
