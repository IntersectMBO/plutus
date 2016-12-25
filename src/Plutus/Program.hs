{-# OPTIONS -Wall #-}





-- | This module defines what it means to be a program in Plutus.

module Plutus.Program where

import Utils.ABT
import Utils.Names
import Utils.Pretty
import Plutus.Term
import PlutusTypes.ConSig
import PlutusTypes.Type

import Data.List (intercalate)





-- | A program is just a series of 'Statement's.

newtype Program = Program [Statement]

instance Show Program where
  show (Program stmts) = intercalate "\n\n" (map show stmts)





-- | A 'Statement' is either a 'TypeDeclaration' or a 'TermDeclaration'.

data Statement
  = TyDecl TypeDeclaration
  | TmDecl TermDeclaration

instance Show Statement where
  show (TyDecl td) = show td
  show (TmDecl td) = show td





-- | A term can be declared either with a simple equality, as in
--
-- > not : Bool -> Bool {
-- >   \b -> case b of {
-- >           True -> False ;
-- >           False -> True
-- >         }
-- > }
--
-- or with a pattern match, as in
--
-- > not : Bool -> Bool {
-- >   not True = False ;
-- >   not False = True
-- > }
--
-- The former is only used internally but is useful to have in mind.

data TermDeclaration
  = TermDeclaration (Sourced String) PolymorphicType Term
  | WhereDeclaration (Sourced String) PolymorphicType [([Pattern],[String],Term)]

instance Show TermDeclaration where
  show (TermDeclaration n ty def) =
    showSourced n ++ " : " ++ pretty ty ++ " { " ++ pretty def ++ " }"
  show (WhereDeclaration n ty preclauses) =
    showSourced n ++ " : " ++ pretty ty ++ " { "
      ++ intercalate " ; " (map showPreclause preclauses)
      ++ " }"
    where
      showPreclause :: ([Pattern],[String],Term) -> String
      showPreclause (ps,_,b) =
        intercalate " " (map pretty ps) ++ " = " ++ pretty b





-- | A type is declared with Haskell-like notation, as in
--
-- > data Bool = { True | False }

data TypeDeclaration
  = TypeDeclaration String [String] [(String,ConSig)]

instance Show TypeDeclaration where
  show (TypeDeclaration tycon params []) =
    "data " ++ tycon ++ concat (map (' ':) params) ++ " end"
  show (TypeDeclaration tycon params alts) =
    "data " ++ tycon ++ concat (map (' ':) params) ++ " = "
      ++ intercalate
           " | "
           [ showAlt c (map body as) | (c, ConSig as _) <- alts ]
      ++ " end"
   where
     showAlt :: String -> [Type] -> String
     showAlt c [] = c
     showAlt c as = c ++ " " ++ unwords (map pretty as)