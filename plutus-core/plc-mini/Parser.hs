{-# LANGUAGE GADTs #-}

-- This module wraps the PLC parser and pretty printer

module Parser where

import           Hutton

import           Language.PlutusCore
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Pretty

import           Control.Monad.Trans.Except
import           Data.Bifunctor
import qualified Data.ByteString.Lazy       as BSL
import           Numeric.Natural

type Prog = Program TyName Name DefaultUni DefaultFun ()
type Tm   = Term TyName Name DefaultUni DefaultFun ()

-- parser

convCon :: Some (ValueOf DefaultUni) -> Maybe Exp
convCon (Some (ValueOf DefaultUniInteger i)) | i >= 0 =
  Just $ Val (fromInteger i)
convCon _ = Nothing

convTm :: Tm -> Maybe Exp
convTm (Constant _ c) = convCon c
convTm (Apply _ (Apply _ (Builtin _ AddInteger) t) u) = do
  e1 <- convTm t
  e2 <- convTm u
  return $ Add e1 e2
convTm _ = Nothing

convProg :: Prog -> Maybe Exp
convProg (Program _ _ t) = convTm t

parseProg :: BSL.ByteString -> Either (ParseError ()) Prog
parseProg = bimap (() <$) (() <$) . runQuote . runExceptT . parseProgram

parseExp :: BSL.ByteString -> Maybe Exp
parseExp b = case parseProg b of
  Left _  -> Nothing
  Right p -> convProg p

-- pretty printer

unconv :: Exp -> Tm
unconv (Val n) = Constant () (Some (ValueOf DefaultUniInteger (toInteger n)))
unconv (Add e1 e2) =
  Apply () (Apply () (Builtin () AddInteger) (unconv e1)) (unconv e2)

pretty :: Exp -> String
pretty e = display $ unconv e
