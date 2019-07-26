{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
-- | Functions for working with the contract interface using typed transactions.
module Language.Plutus.Contract.Typed.Tx where

import           Control.Lens                (at, (^.))
import           Data.Either                 (rights)
import qualified Data.Map                    as Map
import           Data.Maybe                  (fromMaybe)

import qualified Language.Plutus.Contract.Tx as Contract
import qualified Language.PlutusTx           as PlutusTx
import           Ledger                      (TxOut, TxOutRef)
import qualified Ledger                      as L
import           Ledger.AddressMap           (AddressMap)
import qualified Ledger.Typed.Tx             as Typed

-- | Given the pay to script address of the 'ValidatorScript', collect from it
--   all the outputs that match a predicate, using the 'RedeemerScript'.
collectFromScriptFilter ::
    forall a
    . (PlutusTx.Typeable (Typed.DataType a))
    => (TxOutRef -> TxOut -> Bool)
    -> AddressMap
    -> Typed.ScriptInstance a
    -> PlutusTx.CompiledCode (Typed.RedeemerType a)
    -> Contract.UnbalancedTx
collectFromScriptFilter flt am ct@(Typed.Validator vls) red =
    let adr     = L.scriptAddress $ L.ValidatorScript $ L.fromCompiledCode vls
        utxo :: Map.Map TxOutRef TxOut
        utxo    = fromMaybe Map.empty $ am ^. at adr
        ourUtxo :: [(TxOutRef, TxOut)]
        ourUtxo = Map.toList $ Map.filterWithKey flt utxo
        refs :: [TxOutRef]
        refs = fst <$> ourUtxo
        -- We just throw away any outputs at this script address that don't typecheck.
        -- TODO: we should log this, it would make debugging much easier
        typedRefs :: [Typed.TypedScriptTxOutRef a]
        typedRefs = rights $ Typed.typeScriptTxOutRef @a (\ref -> Map.lookup ref utxo) ct <$> refs
        typedIns :: [Typed.TypedScriptTxIn '[] a]
        typedIns = Typed.makeTypedScriptTxIn @a @'[] ct red <$> typedRefs
        -- We need to add many txins and we've done as much checking as we care to, so we switch to TypedTxSomeIns
        fullTx :: Typed.TypedTxSomeIns '[]
        fullTx = Typed.addManyTypedTxIns typedIns Typed.baseTx
        untypedTx :: L.Tx
        -- Need to match to get the existential type out
        untypedTx = case fullTx of
            (Typed.TypedTxSomeIns tx) -> Typed.toUntypedTx tx
    in Contract.fromLedgerTx untypedTx
