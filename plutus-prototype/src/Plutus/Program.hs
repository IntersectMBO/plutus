{-# OPTIONS -Wall #-}





-- | This module defines what it means to be a program in Plutus.

module Plutus.Program where

import           Plutus.Term
import           PlutusTypes.ConSig
import           PlutusTypes.Type
import           Utils.ABT
import           Utils.Names
import           Utils.Pretty
import           Utils.Vars

import           Data.List          (intercalate)





-- | A program is just a series of 'Statement's.

newtype Program = Program [Statement]

instance Show Program where
  show (Program stmts) = intercalate "\n\n" (map show stmts)


substTypeMetasProgram :: [(MetaVar,Type)] -> Program -> Program
substTypeMetasProgram s (Program stmts) =
  Program (map (substTypeMetasStatement s) stmts)





-- | A 'Statement' is either a 'TypeDeclaration' or a 'TermDeclaration'.

data Statement
  = TyDecl TypeDeclaration
  | TmDecl TermDeclaration

instance Show Statement where
  show (TyDecl td) = show td
  show (TmDecl td) = show td


substTypeMetasStatement :: [(MetaVar,Type)] -> Statement -> Statement
substTypeMetasStatement s (TyDecl tydecl) =
  TyDecl (substTypeMetasTypeDecl s tydecl)
substTypeMetasStatement s (TmDecl tmdecl) =
  TmDecl (substTypeMetasTermDecl s tmdecl)





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
  = TermDeclaration (Sourced String) Type Term
  | WhereDeclaration (Sourced String) Type [([Pattern],[String],Term)]

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

termDeclarationName :: TermDeclaration -> Sourced String
termDeclarationName (TermDeclaration n _ _)  = n
termDeclarationName (WhereDeclaration n _ _) = n

substTypeMetasTermDecl
  :: [(MetaVar,Type)] -> TermDeclaration -> TermDeclaration
substTypeMetasTermDecl s (TermDeclaration n a m) =
  TermDeclaration
    n
    (substMetas s a)
    (substTypeMetas s m)
substTypeMetasTermDecl s (WhereDeclaration n a cls) =
  WhereDeclaration
    n
    (substMetas s a)
    [ (ps, xs, substTypeMetas s m)
      | (ps, xs, m) <- cls
      ]






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

substTypeMetasTypeDecl
  :: [(MetaVar,Type)] -> TypeDeclaration -> TypeDeclaration
substTypeMetasTypeDecl s (TypeDeclaration n xs alts) =
  TypeDeclaration
    n
    xs
    [ (c, substMetasConSig s consig)
      | (c, consig) <- alts
      ]
