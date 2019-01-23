{-# LANGUAGE GADTs #-}

module Convert where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           Language.PlutusCore.Parser
import qualified Data.Text                  as T
import           Data.ByteString.Lazy       as BSL

import Data.Either

data RTerm = RVar T.Text
           | RTLambda T.Text RTerm
           | RTApp RTerm
           | RLambda T.Text RTerm
           | RApp RTerm RTerm
  deriving Show

convP :: Program TyName Name a -> RTerm
convP (Program _ _ t) = conv t

conv :: Term TyName Name a -> RTerm
conv (Var _ x)        = RVar (nameString x)
conv (TyAbs _ x _ t)  = RTLambda (nameString $ unTyName x) (conv t)
conv (TyInst _ t _)   = RTApp (conv t)
conv (LamAbs _ x _ t) = RLambda (nameString x) (conv t)
conv (Apply _ t u)    = RApp (conv t) (conv u)