{-# OPTIONS -Wall #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}







module PlutusCore.EvaluatorTypes where

import           PlutusCore.Term
import           Utils.Env
import           Utils.Names

import qualified Data.ByteString.Lazy as BS







data TransactionInfo =
  TransactionInfo
  { txHash      :: BS.ByteString
  , txDistrHash :: BS.ByteString
  }

newtype Petrol = Petrol Int
  deriving (Show,Num,Eq,Ord)

type SourcedEnv = Env (Sourced String) Term
