{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module Plutus.Contract.StateMachine.ThreadToken where

import           PlutusTx.Prelude     hiding (Monoid (..), Semigroup (..))

import           Data.Aeson           (FromJSON, ToJSON)
import           GHC.Generics         (Generic)
import           Ledger               (CurrencySymbol, TxOutRef (..))
import qualified Ledger.Contexts      as V
import           Ledger.Scripts
import qualified Ledger.Typed.Scripts as Scripts
import           Ledger.Value         (TokenName (..), Value (..))
import qualified Ledger.Value         as Value
import qualified PlutusTx
import qualified PlutusTx.AssocMap    as Map
import qualified Prelude              as Haskell

data ThreadToken = ThreadToken
    { ttOutRef         :: TxOutRef
    , ttCurrencySymbol :: CurrencySymbol
    }
    deriving stock (Haskell.Eq, Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

PlutusTx.makeLift ''ThreadToken

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

{-# INLINABLE threadTokenValue #-}
-- | The 'Value' containing exactly the thread token.
threadTokenValue :: CurrencySymbol -> ValidatorHash -> Value
threadTokenValue currency (ValidatorHash vHash) = Value.singleton currency (TokenName vHash) 1

{-# INLINABLE checkThreadToken #-}
checkThreadToken :: Maybe ThreadToken -> ValidatorHash -> Value -> Bool
checkThreadToken Nothing _ _ = True
checkThreadToken (Just threadToken) (ValidatorHash vHash) (Value vl) =
    case Map.toList <$> Map.lookup (ttCurrencySymbol threadToken) vl of
        Just [(TokenName tHash, _)] -> tHash == vHash
        _                           -> False
