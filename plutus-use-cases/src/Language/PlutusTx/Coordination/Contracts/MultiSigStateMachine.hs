{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE DataKinds         #-}
{-# OPTIONS_GHC -O0 #-}
-- | A multisig contract written as a state machine. 
module Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine(
      Params(..)
    , validator
    ) where

import           Ledger                       (ValidatorScript(..))
import qualified Ledger
import           Ledger.Validation            (PendingTx)

import Language.PlutusTx.StateMachine
import Language.PlutusTx.Coordination.Contracts.MultiSig.Stage0

validator :: Params -> ValidatorScript
validator params = ValidatorScript val where
    val = Ledger.applyScript script (Ledger.lifted params)
    
    script = ($$(Ledger.compileScript [||

        \(p :: Params) (ds :: (State, Maybe Input)) (vs :: (State, Maybe Input)) (ptx :: PendingTx) ->
            let 
                trans = $$step p ptx
                sm = StateMachine trans $$stateEq
            in $$(mkValidator) sm ds vs ptx

        ||]))