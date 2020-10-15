{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans       #-}

module Language.Marlowe.ACTUS.AgdaOps where

import           Data.Time                                             (Day)
import           Language.Marlowe                                      (Observation (ValueGT, ValueLT), Value (AddValue, Cond, Constant, MulValue, Scale, SubValue),
                                                                        (%))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms      (ContractRole, DCC)
import           Language.Marlowe.ACTUS.Model.Utility.ContractRoleSign (contractRoleSign)
import           Language.Marlowe.ACTUS.Model.Utility.YearFraction     (yearFraction)
import           Language.Marlowe.ACTUS.Ops
import           Agda.Syntax.Concrete                                  (Expr(..))

instance ActusNum Expr where
    a + b       = undefined
    a - b       = undefined
    a * b       = undefined
    a / b       = undefined

instance DateOps Expr Expr where
    _lt a b = undefined

instance YearFractionOps Day Expr where
    _y = undefined

instance RoleSignOps Expr where
    _r = undefined

