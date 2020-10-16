{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans       #-}

module Language.Marlowe.ACTUS.AgdaOps where

import           Language.Marlowe.ACTUS.Model.Utility.ContractRoleSign (contractRoleSign)
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

one :: Expr
one = Lit NoRange $ LitNat 1

minusone :: Expr
minusone = Lit NoRange $ LitNat (- 1)

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

instance RoleSignOps Expr where
    _r role = if (contractRoleSign role > 0) then one else minusone

