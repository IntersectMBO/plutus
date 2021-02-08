{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyDataDecls      #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
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
import           Data.Text
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

conv :: PlcProgD -> Maybe (Tm Empty)
conv (Program _ _ t) = convTm undefined t


{-
var :: Natural -> Maybe a
var 0 = Nothing
var 1 = Just Nothing
-}
convTm :: (Natural -> a) -> PlcTermD -> Maybe (Tm a)
convTm g (Constant _ c) = convCon c
convTm g (Apply _ (Apply _ (Builtin _ AddInteger) t) u) = do
  e1 <- convTm g t
  e2 <- convTm g u
  return $ Add e1 e2
convTm g (Apply _ t u) = do
  t' <- convTm g t
  u' <- convTm g u
  return (App t' u')
convTm g (Plc.Var _ x) = return $ Lambda.Var (g (unIndex (ndbnIndex x) - 1))
convTm g (LamAbs () _ _ t) = Lam <$> (convTm (\case {0 -> Nothing; n -> Just $ g (n-1)}) t)
convTm g _ = Nothing

parseProg :: BSL.ByteString -> Either (ParseError ()) PlcProgN
parseProg = bimap (() <$) (() <$) . runQuote . runExceptT . parseProgram

parse :: BSL.ByteString -> Maybe (Tm Empty)
parse b = case parseProg b of
  Left _  -> Nothing
  Right p -> case deBruijnify p of
    Left _  -> Nothing
    Right p -> conv p

-- pretty printer

unIndex :: Index -> Natural
unIndex (Index n) = n


tmnames = ['a' .. 'z']



unconv :: Int -> (a -> Name) -> Tm a -> PlcTermN
unconv i g (Val n) = Constant () (Some (ValueOf DefaultUniInteger (toInteger n)))
unconv i g (Add e1 e2) =
  Apply () (Apply () (Builtin () AddInteger) (unconv i g e1)) (unconv i g e2)
unconv i g (Lambda.Var x) = Plc.Var () (g x)
unconv i g (Lam t) = LamAbs () (Name (pack [tmnames !! i]) undefined) (TyBuiltin () (Some (TypeIn DefaultUniInteger)))  (unconv (i+1) (\case {Nothing -> Name (pack [tmnames !! i]) undefined;Just x -> g x}) t)

pretty :: Tm a -> String
pretty e = display $ unconv 0 undefined e
