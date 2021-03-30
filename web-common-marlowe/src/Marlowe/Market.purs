module Marlowe.Market (contractTemplates) where

-- At some point we will want to keep contract templates in a database. In the
-- meantime, this is a simple solution to get things up and running.
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.Market.Escrow as Escrow
import Marlowe.Market.EscrowWithCollateral as EscrowWithCollateral
import Marlowe.Market.ZeroCouponBond as ZeroCouponBond
import Marlowe.Market.CouponBondGuaranteed as CouponBondGuaranteed
import Marlowe.Market.Swap as Swap
import Marlowe.Market.ContractForDifferences as ContractForDifferences

contractTemplates :: Array ContractTemplate
contractTemplates =
  [ Escrow.contractTemplate
  , EscrowWithCollateral.contractTemplate
  , ZeroCouponBond.contractTemplate
  , CouponBondGuaranteed.contractTemplate
  , Swap.contractTemplate
  , ContractForDifferences.contractTemplate
  ]
