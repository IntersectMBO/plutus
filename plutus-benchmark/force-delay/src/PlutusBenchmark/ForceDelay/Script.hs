{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | This module produces the scripts used in the force-delay benchmark.
module PlutusBenchmark.ForceDelay.Script where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (mkConstant)
import PlutusCore.Quote
import PlutusCore.Version
import PlutusPrelude (unsafeFromRight)
import UntypedPlutusCore as UPLC

import Data.Foldable qualified as F
import Data.Text qualified as T

nameToDebruijn
  :: Program Name DefaultUni DefaultFun ()
  -> Program DeBruijn DefaultUni DefaultFun ()
nameToDebruijn (Program ann ver term) =
  Program ann ver
    . termMapNames unNameDeBruijn
    . unsafeFromRight @PLC.FreeVariableError
    $ deBruijnTerm term

nested0 :: Int -> Program DeBruijn DefaultUni DefaultFun ()
nested0 n
  | n <= 0 = error "nested0: n must be positive"
  | otherwise = nameToDebruijn . Program () plcVersion100 . runQuote $ do
      name <- freshName "a"
      let body = LamAbs () name $ Var () name
          inner = foldr (\_ acc -> Delay () acc) body (replicate n ())
          result = F.foldl' (\acc _ -> Force () acc) inner (replicate n ())
      pure result

nested1 :: Int -> Program DeBruijn DefaultUni DefaultFun ()
nested1 n
  | n <= 0 = error "nested1: n must be positive"
  | otherwise = nameToDebruijn . Program () plcVersion100 . runQuote $ do
      names <- traverse (\i -> freshName ("a" <> T.pack (show i))) [1 .. n]
      let body = Var () (last names)
          delayed = foldr (\a acc -> Delay () (LamAbs () a acc)) body names
          args = [mkConstant @Integer () (toInteger i) | i <- [1 .. n]]
      pure $ F.foldl' (\acc arg -> Apply () (Force () acc) arg) delayed args

nested2 :: Int -> Program DeBruijn DefaultUni DefaultFun ()
nested2 n
  | n <= 0 = error "nested2: n must be positive"
  | otherwise = nameToDebruijn . Program () plcVersion100 . runQuote $ do
      namesA <- traverse (\i -> freshName ("a" <> T.pack (show i))) [1 .. n]
      namesB <- traverse (\i -> freshName ("b" <> T.pack (show i))) [1 .. n]
      let body = Var () (last namesA)
          delayed = foldr (\(a, b) acc -> Delay () (LamAbs () a $ LamAbs () b acc)) body (namesA `zip` namesB)
          args = [mkConstant @Integer () (toInteger i) | i <- [1 .. n]]
      pure $ F.foldl' (\acc arg -> Apply () (Apply () (Force () acc) arg) arg) delayed args
