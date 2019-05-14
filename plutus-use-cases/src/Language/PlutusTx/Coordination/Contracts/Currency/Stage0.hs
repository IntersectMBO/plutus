{-# LANGUAGE TemplateHaskell #-}
module Language.PlutusTx.Coordination.Contracts.Currency.Stage0 where

import qualified Language.PlutusTx         as P

import           Ledger.Validation         (TxHash)
import qualified Ledger.Map                as LMap
import qualified Ledger.Map.TH             as LMap.TH
import           Ledger.Value              (CurrencySymbol, TokenName, Value)
import qualified Ledger.Value.TH           as Value.TH

import           Language.Haskell.TH       (Q, TExp)

data Currency = Currency
  { curRefTransactionOutput :: (TxHash, Integer)
  -- ^ Transaction input that must be spent when
  --   the currency is forged.
  , curAmounts              :: LMap.Map TokenName Integer
  -- ^ How many units of each 'TokenName' are to
  --   be forged.
  }

P.makeLift ''Currency

currencyValue :: Q (TExp (CurrencySymbol -> Currency -> Value))
currencyValue = [||
        let currencyValue' :: CurrencySymbol -> Currency -> Value
            currencyValue' s c =
                let
                    Currency _ amts = c
                    values = P.map (\(tn, i) -> ($$(Value.TH.singleton) s tn i)) ($$(LMap.TH.toList) amts)
                in P.foldr $$(Value.TH.plus) $$(Value.TH.zero) values

        in currencyValue'
    ||]
