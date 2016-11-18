{-# OPTIONS -Wall #-}





-- | This module defines what it means to be a program in Plutus Core.

module PlutusCore.Program where

import Utils.Pretty
import PlutusCore.Term

import Data.List (intercalate)





-- | A program is just a series of 'Statement's.

newtype Program = Program [TermDeclaration]

instance Show Program where
  show (Program stmts) =
    "program(" ++ intercalate "," (map show stmts) ++ ")"





-- | A term declaration consists of just a name and a term.

data TermDeclaration
  = TermDeclaration String Term

instance Show TermDeclaration where
  show (TermDeclaration n def) =
    "dec(" ++ n ++ ";" ++ pretty def ++ ")"