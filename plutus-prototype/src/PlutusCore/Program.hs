{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS -Wall #-}





-- | This module defines what it means to be a program in Plutus Core.

module PlutusCore.Program where

import           PlutusCore.Term
import           PlutusTypes.ConSig
import           PlutusTypes.Type
import           Utils.Names
import           Utils.Pretty

import           Data.List          (intercalate)

import           GHC.Generics




-- | A program is some type constructor signatures, constructor signatures,
-- and a series of term declarations.

data Program =
  Program
  { termDeclarations :: [(Sourced String, (Term, Type))]
  }
  deriving (Generic)

instance Show Program where
  show (Program stmts) =
    "program("
      ++ intercalate ","
           [ "dec(" ++ showSourced n
               ++ ";" ++ pretty def
               ++ ";" ++ pretty ty
               ++ ")"
           | (n,(def,ty)) <- stmts
           ]
      ++ ")"
