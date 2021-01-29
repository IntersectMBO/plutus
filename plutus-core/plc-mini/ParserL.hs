{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyDataDecls      #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}

-- This module wraps the PLC parser and pretty printer

module ParserL where

import           Lambda

import           Language.PlutusCore          as Plc
import           Language.PlutusCore.DeBruijn
import           Language.PlutusCore.Error
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Pretty

import           Control.Monad.Trans.Except
import           Data.Bifunctor
import qualified Data.ByteString.Lazy         as BSL
import           Numeric.Natural

type PlcProgN = Program TyName Name DefaultUni DefaultFun ()
type PlcProgD = Program NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun ()

type PlcTermN = Term TyName Name DefaultUni DefaultFun ()
type PlcTermD = Term NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun ()

deBruijnify :: PlcProgN -> Either FreeVariableError PlcProgD
deBruijnify = second (() <$) . runExcept . deBruijnProgram

-- parser

convCon :: Some (ValueOf DefaultUni) -> Maybe (Tm a)
convCon (Some (ValueOf DefaultUniInteger i)) | i >= 0 =
  Just $ Val (fromInteger i)
convCon _ = Nothing

--conv :: PlcProgD -> Maybe (Tm a)
conv (Program _ _ t) = convTm t


class Nat n
instance Nat Empty
instance Nat n => Nat (Maybe n)

succ :: Nat n => n -> (Maybe n)
succ n = Just n

{-
var :: Natural -> Maybe a
var 0 = Nothing
var 1 = Just Nothing
-}
--convTm :: PlcTermD -> Maybe (Tm a)
convTm (Constant _ c) = convCon c
convTm (Apply _ (Apply _ (Builtin _ AddInteger) t) u) = do
  e1 <- convTm t
  e2 <- convTm u
  return $ Add e1 e2
convTm (Plc.Var _ x) = return $ _
convTm _ = Nothing

parseProg :: BSL.ByteString -> Either (ParseError ()) PlcProgN
parseProg = bimap (() <$) (() <$) . runQuote . runExceptT . parseProgram

--parse :: BSL.ByteString -> Maybe (Tm Empty)
parse b = case parseProg b of
  Left _  -> Nothing
  Right p -> case deBruijnify p of
    Left _  -> Nothing
    Right p -> conv p

-- pretty printer

unconv :: Tm a -> PlcTermN
unconv (Val n) = Constant () (Some (ValueOf DefaultUniInteger (toInteger n)))
unconv (Add e1 e2) =
  Apply () (Apply () (Builtin () AddInteger) (unconv e1)) (unconv e2)

pretty :: Tm a -> String
pretty e = display $ unconv e
