{-# OPTIONS -Wall #-}







-- | This module implements constructor signatures, for data declarations.

module Plutus.ConSig where

import Utils.ABT
import Utils.Pretty (pretty)
import Plutus.Type

import Data.List (intercalate)







-- | A constructor signature in this variant is simply a list of argument
-- types and a return type.

data ConSig = ConSig [Scope TypeF] (Scope TypeF)


instance Show ConSig where
  show (ConSig as r) =
    "["
    ++ intercalate "," (names r)
    ++ "]("
    ++ intercalate "," (map (pretty.body) as)
    ++ ")"
    ++ pretty (body r)


conSigH :: [String] -> [Type] -> Type -> ConSig
conSigH ns as r = ConSig (map (scope ns) as) (scope ns r)