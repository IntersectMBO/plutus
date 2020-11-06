{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Language.Marlowe.ACTUS.Agda.AgdaOps() where

import           Language.Marlowe.ACTUS.Ops
import           Agda.Syntax.Common                                    (NamedArg, MaybePlaceholder, NameId(..), noPlaceholder, defaultNamedArg, noFixity')
import           Agda.Syntax.Position                                  (Range'(..), )
import           Agda.Syntax.Literal                                   (Literal(..))
import           Agda.Syntax.Concrete                                  (Expr(..), OpApp(..))
import           Agda.Syntax.Concrete.Name                             (Name(..), QName(..), NameInScope(..), NamePart(..))
import qualified Data.Set                                              as S
import           Data.List.NonEmpty                                    (NonEmpty(..))
import qualified Agda.Syntax.Abstract.Name                             as AName


quickname :: String -> Name
quickname op = Name NoRange NotInScope $ (Id op) :| []

quicknameA :: String -> AName.Name
quicknameA op = AName.Name (NameId 0 0) (quickname op) (quickname op) NoRange noFixity' False

quickarg :: Expr -> NamedArg (MaybePlaceholder (OpApp Expr))
quickarg e = defaultNamedArg $ noPlaceholder $ Ordinary e

zero :: Expr
zero = Paren NoRange $ App NoRange (Ident $ QName $ quickname "+") $ defaultNamedArg $ Lit NoRange $ LitNat 0

one :: Expr
one = Paren NoRange $ App NoRange (Ident $ QName $ quickname "+") $ defaultNamedArg $ Lit NoRange $ LitNat 1

minusone :: Expr
minusone = Paren NoRange $ App NoRange (Ident $ QName $ quickname "-") $ defaultNamedArg $ Lit NoRange $ LitNat 1

instance ActusOps Expr where
    _min a b = Paren NoRange $ App NoRange (App NoRange (Ident $ QName $ quickname "min") (defaultNamedArg a)) (defaultNamedArg b)
    _max a b = Paren NoRange $ App NoRange (App NoRange (Ident $ QName $ quickname "max") (defaultNamedArg a)) (defaultNamedArg b)
    _zero = zero
    _one  = one

instance ActusNum Expr where
    a + b       = Paren NoRange $ OpApp NoRange (QName $ quickname "") (S.singleton $ quicknameA "+") $ (quickarg a) :| [quickarg $ Ident $ QName $ quickname "+", quickarg b]
    a - b       = Paren NoRange $ OpApp NoRange (QName $ quickname "") (S.singleton $ quicknameA "-") $ (quickarg a) :| [quickarg $ Ident $ QName $ quickname "-", quickarg b]
    a * b       = Paren NoRange $ OpApp NoRange (QName $ quickname "") (S.singleton $ quicknameA "*") $ (quickarg a) :| [quickarg $ Ident $ QName $ quickname "*", quickarg b]
    a / b       = Paren NoRange $ OpApp NoRange (QName $ quickname "") (S.singleton $ quicknameA "/") $ (quickarg a) :| [quickarg $ Ident $ QName $ quickname "/", quickarg b]

instance DateOps Expr Expr where
    _lt a b = 
        Paren NoRange $ App NoRange (App NoRange (Ident $ QName $ quickname "pseudoLt") (defaultNamedArg a)) (defaultNamedArg b)  

instance YearFractionOps Expr Expr where
    _y _ start end maturity = 
        Paren NoRange $ App NoRange (App NoRange (App NoRange (Ident $ QName $ quickname "yearFraction") (defaultNamedArg start)) (defaultNamedArg end)) (defaultNamedArg maturity)

instance RoleSignOps Expr Expr where
    _r role = 
        Paren NoRange $ App NoRange (Ident $ QName $ quickname "roleSign") (defaultNamedArg role)

