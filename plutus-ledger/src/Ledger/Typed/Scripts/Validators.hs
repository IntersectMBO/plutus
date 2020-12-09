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
module Ledger.Typed.Scripts.Validators where

import           Data.Kind
import           Data.Void

import           PlutusTx
import           PlutusTx.Prelude

import           Plutus.V1.Ledger.Contexts (PolicyCtx (..), TxInfo (..))
import qualified Plutus.V1.Ledger.Contexts as Validation
import           Plutus.V1.Ledger.Scripts

-- | The type of validators for the given connection type.
type ValidatorType (a :: Type) = DatumType a -> RedeemerType a -> Validation.ValidatorCtx -> Bool

type WrappedValidatorType = Data -> Data -> Data -> ()
type WrappedMonetaryPolicyType = Data -> ()

-- | A class that associates a type standing for a connection type with two types, the type of the redeemer
-- and the data script for that connection type.
class ScriptType (a :: Type) where
    -- | The type of the redeemers of this connection type.
    type RedeemerType a :: Type
    -- | The type of the data of this connection type.
    type DatumType a :: Type

    -- Defaults
    type instance RedeemerType a = ()
    type instance DatumType  a = ()

instance ScriptType Void where
    type RedeemerType Void = Void
    type DatumType Void = Void

data Any

instance ScriptType Any where
    type RedeemerType Any = Data
    type DatumType Any = Data

{- Note [Scripts returning Bool]
It used to be that the signal for validation failure was a script being `error`. This is nice for the validator, since
you can determine whether the script evaluation is error-or-not without having to look at what the result actually
*is* if there is one.

However, from the script author's point of view, it would be nicer to return a Bool, since otherwise you end up doing a
lot of `if realCondition then () else error ()` which is rubbish.

So we changed the result type to be Bool. But now we have to answer the question of how the validator knows what the
result value is. All *sorts* of terms can be True or False in disguise. The easiest way to tell is by reducing it
to the previous problem: apply a function which does a pattern match and returns error in the case of False and ()
otherwise. Then, as before, we just check for error in the overall evaluation.
-}

{-# NOINLINE wrapValidator #-}
wrapValidator
    :: forall d r
    . (IsData d, IsData r)
    => (d -> r -> Validation.ValidatorCtx -> Bool)
    -> WrappedValidatorType
wrapValidator f (fromData -> Just d) (fromData -> Just r) (fromData -> Just p) = check $ f d r p
wrapValidator _ _ _ _                                                          = check False

{-# NOINLINE wrapMonetaryPolicy #-}
wrapMonetaryPolicy
    :: (Validation.PolicyCtx -> Bool)
    -> WrappedMonetaryPolicyType
wrapMonetaryPolicy f (fromData -> Just p) = check $ f p
wrapMonetaryPolicy _ _                    = check False

-- | A monetary policy that checks whether the validator script was run
--   in the forging transaction.
{-# NOINLINE forwardingMPS #-}
forwardingMPS :: ValidatorHash -> MonetaryPolicy
forwardingMPS vshsh =
    mkMonetaryPolicyScript
    $ ($$(PlutusTx.compile [|| \(hsh :: ValidatorHash) -> wrapMonetaryPolicy (forwardToValidator hsh) ||]))
       `PlutusTx.applyCode` PlutusTx.liftCode vshsh

{-# NOINLINE forwardToValidator #-}
forwardToValidator :: ValidatorHash -> PolicyCtx -> Bool
forwardToValidator h PolicyCtx{policyCtxTxInfo=TxInfo{txInfoInputs}} =
    let checkHash (Just (vh, _, _)) = vh == h
        checkHash _                 = False
    in any (checkHash . Validation.txInInfoWitness) txInfoInputs
