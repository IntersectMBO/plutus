{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.Marlowe.Client.Interface(
    MarloweInterface(..),
    marloweInterface,
    compiledMarloweInterface
    ) where

import           Language.Marlowe.Semantics (Accounts, Contract, Money, State, TransactionInput, TransactionOutput)
import qualified Language.Marlowe.Semantics as S
import           PlutusTx                   (CompiledCode)
import qualified PlutusTx

data MarloweInterface =
    MarloweInterface
        { validateBalances   :: State -> Bool
        , totalBalance       :: Accounts -> Money
        , computeTransaction :: TransactionInput -> State -> Contract -> TransactionOutput
        }

marloweInterface :: MarloweInterface
marloweInterface =
    MarloweInterface
        { validateBalances   = S.validateBalances
        , totalBalance       = S.totalBalance
        , computeTransaction = S.computeTransaction
        }

-- | Compiled marlowe implementation
compiledMarloweInterface :: CompiledCode MarloweInterface
compiledMarloweInterface = $$(PlutusTx.compile [|| marloweInterface ||])
