{-# LANGUAGE GADTs #-}

module Parser where

import           Lang

import           Language.PlutusCore
import qualified Language.PlutusCore.Lexer
import qualified Language.PlutusCore.Parser

import           Control.Monad.Trans.Except
import           Data.Bifunctor
import qualified Data.ByteString.Lazy       as BSL
import           Numeric.Natural

type Prog = Language.PlutusCore.Program TyName Name DefaultUni DefaultFun Language.PlutusCore.Lexer.AlexPosn



convCon :: Some (ValueOf DefaultUni) -> Maybe Exp
convCon (Some (ValueOf DefaultUniInteger i)) | i >= 0 = Just $ Val (fromInteger i)
convCon _ = Nothing

conv (Program _ _ t) = convTm t

convTm (Constant _ c) = convCon c
convTm (Apply _ (Apply _ (Builtin _ AddInteger) t) u) = do
  e1 <- convTm t
  e2 <- convTm u
  return $ Add e1 e2
convTm _ = Nothing

parseProg :: BSL.ByteString -> Either (ParseError ()) Prog
parseProg = first (() <$) . runQuote . runExceptT . parseProgram

parse :: BSL.ByteString -> Maybe Exp
parse b = case parseProg b of
  Left _  -> Nothing
  Right p -> conv p
