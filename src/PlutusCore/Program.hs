{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS -Wall #-}





-- | This module defines what it means to be a program in Plutus Core.

module PlutusCore.Program where

import Utils.Pretty
import Utils.Names
import PlutusCore.Term

import Data.List (intercalate)

import GHC.Generics




-- | A program is just a series of 'Statement's.

newtype Program = Program [TermDeclaration]
  deriving (Generic)

instance Show Program where
  show (Program stmts) =
    "program(" ++ intercalate "," (map show stmts) ++ ")"





-- | A term declaration consists of just a name and a term.

data TermDeclaration
  = TermDeclaration (Sourced String) Term
  deriving (Generic)

instance Show TermDeclaration where
  show (TermDeclaration n def) =
    "dec(" ++ showSourced n ++ ";" ++ pretty def ++ ")"