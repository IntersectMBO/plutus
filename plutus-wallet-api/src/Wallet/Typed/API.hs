{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module Wallet.Typed.API where

import qualified Language.PlutusTx    as PlutusTx
import           Ledger.AddressMap
import           Ledger.Tx
import qualified Ledger.Typed.Scripts as Scripts
import qualified Ledger.Typed.Tx      as Typed
import           Ledger.Value
import           Wallet.API           (NodeAPI, SlotRange, WalletAPI, WalletAPIError)
import qualified Wallet.API           as WAPI

import           Control.Lens
import           Control.Monad.Except

import           Data.Either
import qualified Data.Map             as Map
import           Data.Maybe
import qualified Data.Set             as Set
import qualified Data.Text            as T

signTxAndSubmit
    :: forall ins outs m .
    (Monad m, WalletAPI m, NodeAPI m, MonadError WalletAPIError m)
    => Typed.TypedTx ins outs
    -> m (Typed.TypedTx ins outs)
signTxAndSubmit tx = do
    _ <- WAPI.signTxAndSubmit $ Typed.toUntypedTx tx
    pure tx

makeScriptPayment
    :: forall a m .
    (Monad m, WalletAPI m, MonadError WalletAPIError m, PlutusTx.IsData (Scripts.DataType a))
    => Scripts.ScriptInstance a
    -> SlotRange
    -> Value
    -> Scripts.DataType a
    -> m (Typed.TypedTx '[] '[a])
makeScriptPayment ct range v ds = do
    (i, ownChange) <- WAPI.createPaymentWithChange v
    (ins, change) <- either (WAPI.throwOtherError . T.pack . show) pure $ do
        ins <- traverse Typed.typePubKeyTxIn (Set.toList i)
        change <- traverse Typed.typePubKeyTxOut ownChange
        pure (ins, change)
    let out = Typed.makeTypedScriptTxOut @a ct ds v
        tyTx = Typed.addTypedTxOut @'[] @'[] @a out (Typed.baseTx { Typed.tyTxValidRange = range, Typed.tyTxPubKeyTxIns = ins, Typed.tyTxPubKeyTxOuts = maybeToList change })
    pure tyTx

payToScript
    :: forall a m .
    (WalletAPI m, NodeAPI m, MonadError WalletAPIError m, PlutusTx.IsData (Scripts.DataType a))
    => Scripts.ScriptInstance a
    -> SlotRange
    -> Value
    -> Scripts.DataType a
    -> m (Typed.TypedTx '[] '[a])
payToScript ct range v ds = makeScriptPayment ct range v ds >>= signTxAndSubmit

payToScript_
    :: forall a m .
    (WalletAPI m, NodeAPI m, MonadError WalletAPIError m, PlutusTx.IsData (Scripts.DataType a))
    => Scripts.ScriptInstance a
    -> SlotRange
    -> Value
    -> Scripts.DataType a
    -> m ()
payToScript_ ct range v ds = void $ payToScript ct range v ds

spendScriptOutputs
    :: forall a m
    . (Monad m, WalletAPI m, PlutusTx.IsData (Scripts.DataType a), PlutusTx.IsData (Scripts.RedeemerType a))
    => Scripts.ScriptInstance a
    -> Scripts.RedeemerType a
    -> m [Typed.TypedScriptTxIn a]
spendScriptOutputs ct red = do
    am <- WAPI.watchedAddresses
    let
        addr = Scripts.scriptAddress ct
        utxo :: Map.Map TxOutRef TxOutTx
        utxo = fromMaybe Map.empty $ am ^. at addr
        typeRef :: TxOutRef -> Either Typed.ConnectionError (Typed.TypedScriptTxOutRef a)
        typeRef = Typed.typeScriptTxOutRef @a (\refq -> Map.lookup refq utxo) ct
        typedRefs :: [Typed.TypedScriptTxOutRef a]
        typedRefs = rights $ typeRef <$> Map.keys utxo
        typedIns :: [Typed.TypedScriptTxIn a]
        typedIns = Typed.makeTypedScriptTxIn @a ct red <$> typedRefs

    pure typedIns

-- | Given the pay to script address of the 'Validator', collect from it
--   all the outputs that match a predicate, using the 'RedeemerValue'.
collectFromScriptFilter ::
    forall a
    . (PlutusTx.IsData (Scripts.DataType a), PlutusTx.IsData (Scripts.RedeemerType a))
    => (TxOutRef -> TxOutTx -> Bool)
    -> AddressMap
    -> Scripts.ScriptInstance a
    -> Scripts.RedeemerType a
    -> Typed.TypedTxSomeIns '[]
collectFromScriptFilter flt am si red =
    let adr     = Scripts.scriptAddress si
        utxo :: Map.Map TxOutRef TxOutTx
        utxo    = fromMaybe Map.empty $ am ^. at adr
        ourUtxo :: Map.Map TxOutRef TxOutTx
        ourUtxo = Map.filterWithKey flt utxo
        -- We just throw away any outputs at this script address that don't typecheck.
        -- TODO: we should log this, it would make debugging much easier
        typedRefs :: [Typed.TypedScriptTxOutRef a]
        typedRefs = rights $ Typed.typeScriptTxOutRef @a (\ref -> Map.lookup ref utxo) si <$> Map.keys ourUtxo
        typedIns :: [Typed.TypedScriptTxIn a]
        typedIns = Typed.makeTypedScriptTxIn @a si red <$> typedRefs
    -- We need to add many txins and we've done as much checking as we care to, so we switch to TypedTxSomeIns
    in Typed.addManyTypedTxIns typedIns Typed.baseTx
