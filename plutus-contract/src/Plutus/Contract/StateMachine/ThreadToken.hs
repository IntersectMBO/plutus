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

import           Control.Lens
import           PlutusTx.Prelude     hiding (Monoid (..), Semigroup (..))

import           Plutus.Contract      as Contract

import           Ledger               (CurrencySymbol, PubKeyHash, TxId, TxOutRef (..), ValidatorHash, pubKeyHash,
                                       scriptCurrencySymbol, txId)
import qualified Ledger.Ada           as Ada
import qualified Ledger.Constraints   as Constraints
import qualified Ledger.Contexts      as V
import           Ledger.Scripts
import qualified PlutusTx             as PlutusTx

import qualified Ledger.Typed.Scripts as Scripts
import           Ledger.Value         (AssetClass, TokenName (..), Value)
import qualified Ledger.Value         as Value

import           Data.Aeson           (FromJSON, ToJSON)
import qualified Data.Map             as Map
import           Data.Semigroup       (Last (..))
import           GHC.Generics         (Generic)
import qualified PlutusTx.AssocMap    as AssocMap
import           Prelude              (Semigroup (..))
import qualified Prelude              as Haskell

validate :: (ValidatorHash, Bool) -> V.ScriptContext -> Bool
validate (vHash, burn) ctx@V.ScriptContext{V.scriptContextTxInfo=txinfo} =
    let
        ownSymbol = V.ownCurrencySymbol ctx

        minted = V.txInfoForge txinfo
        expected = if burn then inv (threadTokenValue ownSymbol vHash) else threadTokenValue ownSymbol vHash

        -- True if the pending transaction mints the amount of
        -- currency that we expect
        mintOK =
            let v = expected == minted
            in traceIfFalse "Value minted different from expected" v

    in mintOK


curPolicy :: MintingPolicy
curPolicy = mkMintingPolicyScript $
    $$(PlutusTx.compile [|| Scripts.wrapMintingPolicy validate ||])

currencySymbol :: CurrencySymbol
currencySymbol = scriptCurrencySymbol curPolicy

{-# INLINABLE threadTokenValue #-}
-- | The 'Value' containing exactly the thread token.
threadTokenValue :: CurrencySymbol -> ValidatorHash -> Value
threadTokenValue cur (ValidatorHash vHash) = Value.singleton cur (TokenName vHash) 1
