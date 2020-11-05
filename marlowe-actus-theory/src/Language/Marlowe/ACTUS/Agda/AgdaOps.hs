{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Language.Marlowe.ACTUS.Agda.AgdaOps() where

import           Language.Marlowe.ACTUS.Ops
import           Agda.Syntax.Common                                    (NamedArg, MaybePlaceholder, noPlaceholder, defaultNamedArg)
import           Agda.Syntax.Position                                  (Range'(..))
import           Agda.Syntax.Literal                                   (Literal(..))
import           Agda.Syntax.Concrete                                  (Expr(..), OpApp(..))
import           Agda.Syntax.Concrete.Name                             (Name(..), QName(..), NameInScope(..), NamePart(..))
import qualified Data.Set                                              as S
import           Data.List.NonEmpty                                    (NonEmpty(..))

quickname :: String -> Name
quickname op = Name NoRange NotInScope $ (Id op) :| []

quickarg :: Expr -> NamedArg (MaybePlaceholder (OpApp Expr))
quickarg e = defaultNamedArg $ noPlaceholder $ Ordinary e

zero :: Expr
zero = Lit NoRange $ LitNat 0

one :: Expr
one = Lit NoRange $ LitNat 0

minusone :: Expr
minusone = Lit NoRange $ LitNat (- 1)

instance ActusOps Expr where
    _min a b = App NoRange (App NoRange (Ident $ QName $ quickname "min") (defaultNamedArg a)) (defaultNamedArg b)
    _max a b = App NoRange (App NoRange (Ident $ QName $ quickname "max") (defaultNamedArg a)) (defaultNamedArg b)
    _zero = zero
    _one  = one

instance ActusNum Expr where
    a + b       = OpApp NoRange (QName $ quickname "+") (S.empty) $ (quickarg a) :| [quickarg b]
    a - b       = OpApp NoRange (QName $ quickname "-") (S.empty) $ (quickarg a) :| [quickarg b]
    a * b       = OpApp NoRange (QName $ quickname "*") (S.empty) $ (quickarg a) :| [quickarg b]
    a / b       = OpApp NoRange (QName $ quickname "/") (S.empty) $ (quickarg a) :| [quickarg b]

instance DateOps Expr Expr where
    _lt a b = 
        App NoRange (App NoRange (Ident $ QName $ quickname "pseudoLt") (defaultNamedArg a)) (defaultNamedArg b)  

instance YearFractionOps Expr Expr where
    _y _ start end maturity = 
        App NoRange (App NoRange (App NoRange (Ident $ QName $ quickname "yearFraction") (defaultNamedArg start)) (defaultNamedArg end)) (defaultNamedArg maturity)

instance RoleSignOps Expr Expr where
    _r role = 
        App NoRange (Ident $ QName $ quickname "roleSign") (defaultNamedArg role)

