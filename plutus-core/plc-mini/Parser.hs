{-# LANGUAGE GADTs #-}

module Parser where

import           Lang

import           Language.PlutusCore
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Pretty

import           Control.Monad.Trans.Except
import           Data.Bifunctor
import qualified Data.ByteString.Lazy       as BSL
import           Numeric.Natural

type Prog = Program TyName Name DefaultUni DefaultFun AlexPosn
type Tm   = Term TyName Name DefaultUni DefaultFun ()
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

-- pretty printer

unconv :: Exp -> Tm
unconv (Val n) = Constant () (Some (ValueOf DefaultUniInteger (toInteger n)))
unconv (Add e1 e2) =
  Apply () (Apply () (Builtin () AddInteger) (unconv e1)) (unconv e2)

pretty :: Exp -> String
pretty e = display $ unconv e
