{-# LANGUAGE GADTs #-}

module Untyped where

import           PlutusCore.Default
import           PlutusCore.Universe
import           UntypedPlutusCore

import           Data.ByteString     as BS
import           Data.Text           as T
import           GHC.Natural


-- Untyped (Raw) syntax

data UTerm = UVar Integer
           | ULambda UTerm
           | UApp UTerm UTerm
           | UCon UConstant
           | UError
           | UBuiltin DefaultFun
           | UDelay UTerm
           | UForce UTerm
           deriving Show

data UConstant = UConInt Integer
               | UConBS BS.ByteString
               | UConStr T.Text
               | UConBool Bool
               | UConChar Char
               | UConUnit
               deriving Show

unIndex :: Index -> Integer
unIndex (Index n) = naturalToInteger n

convP :: Program NamedDeBruijn DefaultUni DefaultFun a -> UTerm
convP (Program _ _ t) = conv t

convC :: Some (ValueOf DefaultUni) -> UConstant
convC (Some (ValueOf DefaultUniInteger    i)) = UConInt i
convC (Some (ValueOf DefaultUniByteString b)) = UConBS b
convC (Some (ValueOf DefaultUniString     s)) = UConStr (T.pack s)
convC (Some (ValueOf DefaultUniChar       c)) = UConChar c
convC (Some (ValueOf DefaultUniUnit       u)) = UConUnit
convC (Some (ValueOf DefaultUniBool       b)) = UConBool b

conv :: Term NamedDeBruijn DefaultUni DefaultFun a -> UTerm
conv (Var _ x)      = UVar (unIndex (ndbnIndex x) - 1)
conv (LamAbs _ _ t) = ULambda (conv t)
conv (Apply _ t u)  = UApp (conv t) (conv u)
conv (Builtin _ b)  = UBuiltin b
conv (Constant _ c) = UCon (convC c)
conv (Error _)      = UError
conv (Delay _ t)    = UDelay (conv t)
conv (Force _ t)    = UForce (conv t)

uconvC :: UConstant -> Some (ValueOf DefaultUni)
uconvC (UConInt i)  = Some (ValueOf DefaultUniInteger    i)
uconvC (UConBS b)   = Some (ValueOf DefaultUniByteString b)
uconvC (UConStr s)  = Some (ValueOf DefaultUniString     $ T.unpack s)
uconvC (UConChar c) = Some (ValueOf DefaultUniChar       c)
uconvC UConUnit     = Some (ValueOf DefaultUniUnit       ())
uconvC (UConBool b) = Some (ValueOf DefaultUniBool       b)

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
uconv i (UCon u)     = Constant () (uconvC u)
uconv i UError       = Error ()
uconv i (UBuiltin b) = Builtin () b
uconv i (UDelay t)   = Delay () (uconv i t)
uconv i (UForce t)   = Force () (uconv i t)
