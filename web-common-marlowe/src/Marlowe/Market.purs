module Marlowe.Market (contractTemplates) where

-- At some point we will want to keep contract templates in a database. In the
-- meantime, this is a simple solution to get things up and running.
import Examples.PureScript.ContractForDifferences as ContractForDifferences
import Examples.PureScript.ContractForDifferencesWithOracle as ContractForDifferencesWithOracle
import Examples.PureScript.CouponBondGuaranteed as CouponBondGuaranteed
import Examples.PureScript.Escrow as Escrow
import Examples.PureScript.EscrowWithCollateral as EscrowWithCollateral
import Examples.PureScript.Swap as Swap
import Examples.PureScript.ZeroCouponBond as ZeroCouponBond
import Marlowe.Extended.Template (ContractTemplate)

contractTemplates :: Array ContractTemplate
contractTemplates =
  [ Escrow.contractTemplate
  , EscrowWithCollateral.contractTemplate
  , ZeroCouponBond.contractTemplate
  , CouponBondGuaranteed.contractTemplate
  , Swap.contractTemplate
  , ContractForDifferences.contractTemplate
  , ContractForDifferencesWithOracle.contractTemplate
  ]
