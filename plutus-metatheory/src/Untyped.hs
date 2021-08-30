{-# LANGUAGE GADTs #-}

module Untyped where

import           PlutusCore.Data
import           PlutusCore.Default
import           UntypedPlutusCore

import           Data.ByteString    as BS
import           Data.Text          as T
import           GHC.Natural
import           Universe


-- Untyped (Raw) syntax

data UTerm = UVar Integer
           | ULambda UTerm
           | UApp UTerm UTerm
           | UCon (Some (ValueOf DefaultUni))
           | UError
           | UBuiltin DefaultFun
           | UDelay UTerm
           | UForce UTerm
           deriving Show

unIndex :: Index -> Integer
unIndex (Index n) = naturalToInteger n

convP :: Program NamedDeBruijn DefaultUni DefaultFun a -> UTerm
convP (Program _ _ t) = conv t

conv :: Term NamedDeBruijn DefaultUni DefaultFun a -> UTerm
conv (Var _ x)      = UVar (unIndex (ndbnIndex x) - 1)
conv (LamAbs _ _ t) = ULambda (conv t)
conv (Apply _ t u)  = UApp (conv t) (conv u)
conv (Builtin _ b)  = UBuiltin b
conv (Constant _ c) = UCon c
conv (Error _)      = UError
conv (Delay _ t)    = UDelay (conv t)
conv (Force _ t)    = UForce (conv t)

tmnames = ['a' .. 'z']

uconv ::  Int -> UTerm -> Term NamedDeBruijn DefaultUni DefaultFun ()
uconv i (UVar x)     = Var
  ()
  (NamedDeBruijn (T.pack [tmnames !! (i - 1 - fromIntegral x)])
                 (Index (naturalFromInteger x)))
uconv i (ULambda t)  = LamAbs
  ()
  (NamedDeBruijn (T.pack [tmnames !! i]) (Index 0))
  (uconv (i+1) t)
uconv i (UApp t u)   = Apply () (uconv i t) (uconv i u)
uconv i (UCon c)     = Constant () c
uconv i UError       = Error ()
uconv i (UBuiltin b) = Builtin () b
uconv i (UDelay t)   = Delay () (uconv i t)
uconv i (UForce t)   = Force () (uconv i t)
