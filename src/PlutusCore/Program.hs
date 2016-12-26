{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS -Wall #-}





-- | This module defines what it means to be a program in Plutus Core.

module PlutusCore.Program where

import Utils.Pretty
import Utils.Names
import PlutusCore.Term
import PlutusTypes.ConSig
import PlutusTypes.Type

import Data.List (intercalate)

import GHC.Generics




-- | A program is some type constructor signatures, constructor signatures,
-- and a series of term declarations.

data Program =
  Program
  { typeConstructors :: [(String,TyConSig)]
  , constructors :: [(String,ConSig)]
  , termDeclarations :: [(Sourced String, (Term, PolymorphicType))]
  }
  deriving (Generic)

instance Show Program where
  show (Program tycons cons stmts) =
    "program("
      ++ intercalate ","
           [ "tyConSig(" ++ n ++ ";" ++ show tyConSig ++ ")"
           | (n,tyConSig) <- tycons
           ]
      ++ ";"
      ++ intercalate ","
           [ "conSig(" ++ n ++ ";" ++ show conSig ++ ")"
           | (n,conSig) <- cons
           ]
      ++ ";"
      ++ intercalate ","
           [ "dec(" ++ showSourced n
               ++ ";" ++ pretty def
               ++ ";" ++ pretty ty
               ++ ")"
           | (n,(def,ty)) <- stmts
           ]
      ++ ")"