{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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
    a + b       = a Prelude.+ b
    a - b       = a Prelude.- b
    a * b       = a Prelude.* b
    a / b       = a Prelude./ b

instance DateOps Expr Expr where
    _lt a b = undefined

instance YearFractionOps Day Double where
    _y = undefined

instance RoleSignOps Double where
    _r = undefined

