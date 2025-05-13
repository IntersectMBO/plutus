{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
-- {-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:certify=FWSTCert #-}

module PlutusBenchmark.V2.Data.ForwardWithStakeTrick where

import PlutusLedgerApi.Data.V2
import PlutusTx qualified
import PlutusTx.BuiltinList qualified as BuiltinList
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Data.AssocMap qualified as Map
import PlutusTx.Plugin ()
import PlutusTx.Prelude qualified as PlutusTx

-- The 'AsData' version of a script which validates that the stake credential is in
-- the withdrawal map.
-- The "trick" is that, if it exists, there is a high probability of the stake
-- credential being either the first or the second element of the map.
forwardWithStakeTrick :: BuiltinData -> BuiltinData -> ()
forwardWithStakeTrick obsScriptCred ctx =
  case PlutusTx.unsafeFromBuiltinData ctx of
    ScriptContext { scriptContextTxInfo = TxInfo { txInfoWdrl } } ->
      let txInfoWdrl' = Map.toBuiltinList txInfoWdrl
          wdrlAtZero = BI.fst $ BI.head txInfoWdrl'
          rest = BI.tail txInfoWdrl'
          wdrlAtOne = BI.fst $ BI.head rest
      in
        if PlutusTx.equalsData obsScriptCred wdrlAtZero
          || PlutusTx.equalsData obsScriptCred wdrlAtOne
          then ()
          else
            if BuiltinList.any (PlutusTx.equalsData obsScriptCred . BI.fst) rest
              then ()
              else PlutusTx.traceError "not found"
{-# INLINABLE forwardWithStakeTrick #-}

mkForwardWithStakeTrickCode
  :: StakingCredential
  -> ScriptContext
  -> PlutusTx.CompiledCode ()
mkForwardWithStakeTrickCode cred ctx =
  let c = PlutusTx.toBuiltinData cred
      sc = PlutusTx.toBuiltinData ctx
  in $$(PlutusTx.compile [|| forwardWithStakeTrick ||])
       `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef c
       `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef sc
