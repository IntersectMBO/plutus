{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module Untyped where

import PlutusCore.Data hiding (Constr)
import PlutusCore.Default
import UntypedPlutusCore

import Data.ByteString as BS hiding (map)
import Data.Text as T hiding (map)
import Data.Word (Word64)
import GHC.Exts (IsList (..))
import Universe

-- Untyped (Raw) syntax

data UTerm = UVar Integer
           | ULambda UTerm
           | UApp UTerm UTerm
           | UCon (Some (ValueOf DefaultUni))
           | UError
           | UBuiltin DefaultFun
           | UDelay UTerm
           | UForce UTerm
           | UConstr Integer [UTerm]
           | UCase UTerm [UTerm]
           deriving Show

unIndex :: Index -> Integer
unIndex (Index n) = toInteger n

convP :: Program NamedDeBruijn DefaultUni DefaultFun a -> UTerm
convP (Program _ _ t) = conv t

conv :: Term NamedDeBruijn DefaultUni DefaultFun a -> UTerm
conv (Var _ x)       = UVar (unIndex (ndbnIndex x) - 1)
conv (LamAbs _ _ t)  = ULambda (conv t)
conv (Apply _ t u)   = UApp (conv t) (conv u)
conv (Builtin _ b)   = UBuiltin b
conv (Constant _ c)  = UCon c
conv (Error _)       = UError
conv (Delay _ t)     = UDelay (conv t)
conv (Force _ t)     = UForce (conv t)
conv (Constr _ i es) = UConstr (toInteger i) (toList (fmap conv es))
conv (Case _ arg cs) = UCase (conv arg) (toList (fmap conv cs))

tmnames = ['a' .. 'z']

uconv ::  Int -> UTerm -> Term NamedDeBruijn DefaultUni DefaultFun ()
uconv i (UVar x)     = Var
  ()
  (NamedDeBruijn (T.pack [tmnames !! (i - 1 - fromInteger x)])
                -- PLC's debruijn starts counting from 1, while in the metatheory it starts from 0.
                 (Index (fromInteger x + 1)))
uconv i (ULambda t)  = LamAbs
  ()
  (NamedDeBruijn (T.pack [tmnames !! i]) deBruijnInitIndex)
  (uconv (i+1) t)
uconv i (UApp t u)     = Apply () (uconv i t) (uconv i u)
uconv i (UCon c)       = Constant () c
uconv i UError         = Error ()
uconv i (UBuiltin b)   = Builtin () b
uconv i (UDelay t)     = Delay () (uconv i t)
uconv i (UForce t)     = Force () (uconv i t)
uconv i (UConstr j xs) = Constr () (fromInteger j) (fromList (fmap (uconv i) xs))
uconv i (UCase t xs)   = Case () (uconv i t) (fromList (fmap (uconv i) xs))

