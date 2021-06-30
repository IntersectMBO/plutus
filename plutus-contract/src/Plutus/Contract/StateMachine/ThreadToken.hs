{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE MonoLocalBinds     #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE ViewPatterns       #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module Plutus.Contract.StateMachine.ThreadToken where

import           PlutusTx.Prelude     hiding (Monoid (..), Semigroup (..))

import           Ledger               (CurrencySymbol, TxOutRef (..), scriptCurrencySymbol)
import qualified Ledger.Contexts      as V
import           Ledger.Scripts
import qualified PlutusTx             as PlutusTx

import qualified Ledger.Typed.Scripts as Scripts
import           Ledger.Value         (TokenName (..), Value)
import qualified Ledger.Value         as Value

validate :: TxOutRef -> (ValidatorHash, Bool) -> V.ScriptContext -> Bool
validate (TxOutRef refHash refIdx) (vHash, burn) ctx@V.ScriptContext{V.scriptContextTxInfo=txinfo} =
    let
        ownSymbol = V.ownCurrencySymbol ctx

        minted = V.txInfoForge txinfo
        expected = if burn
            then inv (threadTokenValue ownSymbol vHash)
            else      threadTokenValue ownSymbol vHash

        -- True if the pending transaction mints the amount of
        -- currency that we expect
        mintOK =
            let v = expected == minted
            in traceIfFalse "Value minted different from expected" v

        -- True if the pending transaction spends the output
        -- identified by @(refHash, refIdx)@
        txOutputSpent =
            let v = V.spendsOutput txinfo refHash refIdx
            in  traceIfFalse "Pending transaction does not spend the designated transaction output" v

    in mintOK && (burn || txOutputSpent)


curPolicy :: TxOutRef -> MintingPolicy
curPolicy outRef = mkMintingPolicyScript $
    $$(PlutusTx.compile [|| \r -> Scripts.wrapMintingPolicy (validate r) ||])
        `PlutusTx.applyCode`
            PlutusTx.liftCode outRef

currencySymbol :: TxOutRef -> CurrencySymbol
currencySymbol outRef = scriptCurrencySymbol (curPolicy outRef)

{-# INLINABLE threadTokenValue #-}
-- | The 'Value' containing exactly the thread token.
threadTokenValue :: CurrencySymbol -> ValidatorHash -> Value
threadTokenValue cur (ValidatorHash vHash) = Value.singleton cur (TokenName vHash) 1
