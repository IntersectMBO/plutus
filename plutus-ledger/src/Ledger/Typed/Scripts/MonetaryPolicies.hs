{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Ledger.Typed.Scripts.MonetaryPolicies (
    WrappedMonetaryPolicyType
    , wrapMonetaryPolicy
    , mkForwardingMonetaryPolicy
    ) where

import           PlutusTx
import           PlutusTx.Prelude

import           Plutus.V1.Ledger.Address    (Address (..))
import           Plutus.V1.Ledger.Contexts   (ScriptContext (..), ScriptPurpose (..), TxInfo (..))
import qualified Plutus.V1.Ledger.Contexts   as Validation
import           Plutus.V1.Ledger.Credential (Credential (..))
import           Plutus.V1.Ledger.Scripts
import           Plutus.V1.Ledger.Tx         (TxOut (..))

type WrappedMonetaryPolicyType = Data -> ()

-- TODO: in due course when we have monetary policies with redeemers we should add a TypedMonetaryPolicy interface here

{-# INLINABLE wrapMonetaryPolicy #-}
wrapMonetaryPolicy
    :: (Validation.ScriptContext -> Bool)
    -> WrappedMonetaryPolicyType
wrapMonetaryPolicy f (fromData -> Just p) = check $ f p
wrapMonetaryPolicy _ _                    = check False

-- | A monetary policy that checks whether the validator script was run
--   in the forging transaction.
mkForwardingMonetaryPolicy :: ValidatorHash -> MonetaryPolicy
mkForwardingMonetaryPolicy vshsh =
    mkMonetaryPolicyScript
    $ ($$(PlutusTx.compile [|| \(hsh :: ValidatorHash) -> wrapMonetaryPolicy (forwardToValidator hsh) ||]))
       `PlutusTx.applyCode` PlutusTx.liftCode vshsh

{-# INLINABLE forwardToValidator #-}
forwardToValidator :: ValidatorHash -> ScriptContext -> Bool
forwardToValidator h ScriptContext{scriptContextTxInfo=TxInfo{txInfoInputs}, scriptContextPurpose=Minting _} =
    let checkHash TxOut{txOutAddress=Address{addressCredential=ScriptCredential vh}} = vh == h
        checkHash _                                                                  = False
    in any (checkHash . Validation.txInInfoResolved) txInfoInputs
forwardToValidator _ _ = False
