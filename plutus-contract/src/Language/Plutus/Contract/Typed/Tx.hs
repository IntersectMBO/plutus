{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- | Functions for working with the contract interface using typed transactions.
module Language.Plutus.Contract.Typed.Tx where

import qualified Language.Plutus.Contract.Tx as Contract
import qualified Language.PlutusTx           as PlutusTx
import           Ledger                      (TxOut, TxOutRef)
import qualified Ledger                      as L
import           Ledger.AddressMap           (AddressMap)
import qualified Ledger.Typed.Scripts        as Scripts
import qualified Ledger.Typed.Tx             as Typed

import qualified Wallet.Typed.API            as Typed

-- | Given the pay to script address of the 'ValidatorScript', collect from it
--   all the outputs that match a predicate, using the 'RedeemerScript'.
collectFromScriptFilter ::
    forall a
    . (PlutusTx.IsData (Scripts.DataType a), PlutusTx.IsData (Scripts.RedeemerType a))
    => (TxOutRef -> TxOut -> Bool)
    -> AddressMap
    -> Scripts.ScriptInstance a
    -> Scripts.RedeemerType a
    -> Contract.UnbalancedTx
collectFromScriptFilter flt am si red =
    let typed = Typed.collectFromScriptFilter flt am si red
        untypedTx :: L.Tx
        -- Need to match to get the existential type out
        untypedTx = case typed of
            (Typed.TypedTxSomeIns tx) -> Typed.toUntypedTx tx
    in Contract.fromLedgerTx untypedTx
