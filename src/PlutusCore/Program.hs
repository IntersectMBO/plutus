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
  , termDeclarations :: [TermDeclaration]
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
      ++ intercalate "," (map show stmts)
      ++ ")"





-- | A term declaration is a name, a term to define the name as, and its type.

data TermDeclaration
  = TermDeclaration (Sourced String) Term Type
  deriving (Generic)

instance Show TermDeclaration where
  show (TermDeclaration n def ty) =
    "dec(" ++ showSourced n ++ ";" ++ pretty def ++ ";" ++ pretty ty ++ ")"


lookupDeclaration :: Sourced String -> [TermDeclaration] -> Maybe (Term,Type)
lookupDeclaration n0 decls =
  lookup n0 [ (n,(m,ty)) | TermDeclaration n m ty <- decls ]