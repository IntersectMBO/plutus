{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module PlutusBenchmark.V2.Data.ScriptContexts where

import PlutusLedgerApi.Data.V2
import PlutusLedgerApi.V1.Data.Address
import PlutusLedgerApi.V1.Data.Value
import PlutusTx qualified
import PlutusTx.BuiltinList qualified as BuiltinList
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Builtins.HasOpaque (stringToBuiltinByteString)
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Data.AssocMap qualified as Map
import PlutusTx.Data.List qualified as DataList
import PlutusTx.Plugin ()
import PlutusTx.Prelude qualified as PlutusTx

-- | A very crude deterministic generator for 'ScriptContext's with size
-- approximately proportional to the input integer.
mkScriptContext :: Integer -> ScriptContext
mkScriptContext i =
  ScriptContext
    (mkTxInfo i)
    (Spending (TxOutRef (TxId "") 0))

mkScriptContextWithStake
  :: Integer
  -> Integer
  -> Maybe (StakingCredential, Int)
  -> ScriptContext
mkScriptContextWithStake i j cred =
  ScriptContext
    (mkTxInfoWithStake i j cred)
    (Spending (TxOutRef (TxId "") 0))

mkTxInfo :: Integer -> TxInfo
mkTxInfo i = TxInfo {
  txInfoInputs=mempty,
  txInfoReferenceInputs=mempty,
  txInfoOutputs=DataList.map mkTxOut (DataList.fromSOP ([1 .. i] :: [Integer])),
  txInfoFee=mempty,
  txInfoMint=mempty,
  txInfoDCert=mempty,
  txInfoWdrl=Map.empty,
  txInfoValidRange=always,
  txInfoSignatories=mempty,
  txInfoRedeemers=Map.empty,
  txInfoData=Map.empty,
  txInfoId=TxId ""
  }

mkTxInfoWithStake
  :: Integer
  -> Integer
  -> Maybe (StakingCredential, Int)
  -> TxInfo
mkTxInfoWithStake i j cred =
  (mkTxInfo i) { txInfoWdrl = mkStakeMap j cred }

-- | A very crude deterministic generator for maps of stake credentials with size
-- approximately proportional to the input integer. If a specific credential is provided, it
-- is inserted at the provided index.
mkStakeMap
  :: Integer
  -> Maybe (StakingCredential, Int)
  -> Map.Map StakingCredential Integer
mkStakeMap j mCred =
  Map.unsafeFromSOPList
  $ case mCred of
      Just (cred, ix) ->
        insertAt cred ix genValues
      Nothing ->
        genValues
  where
    genValues =
      (\i ->
        ( mkStakingCredential ("testCred" <> show i)
        , i
        )
      )
      <$> [1..j]
    insertAt x i xs =
      take i xs <> [(x, 1000)] <> drop i xs

mkStakingCredential :: String -> StakingCredential
mkStakingCredential str =
  StakingHash
  . PubKeyCredential
  . PubKeyHash
  . stringToBuiltinByteString
  $ str


mkTxOut :: Integer -> TxOut
mkTxOut i = TxOut {
  txOutAddress=pubKeyHashAddress (PubKeyHash ""),
  txOutValue=mkValue i,
  txOutDatum=NoOutputDatum,
  txOutReferenceScript=Nothing
  }

mkValue :: Integer -> Value
mkValue i = assetClassValue (assetClass adaSymbol adaToken) i

-- This example decodes the script context (which is O(size-of-context) work), and then also
-- does some work that's roughly proportional to the size of the script context (counting the
-- outputs). This should be a somewhat realistic example where a reasonable chunk of work is
-- done in addition to decoding.
checkScriptContext1 :: PlutusTx.BuiltinData -> ()
checkScriptContext1 d =
  -- Bang pattern to ensure this is forced, probably not necesssary
  -- since we do use it later
  let !sc = PlutusTx.unsafeFromBuiltinData d
      ScriptContext txi _ = sc
  in
  if DataList.length (txInfoOutputs txi) `PlutusTx.modInteger` 2 PlutusTx.== 0
  then ()
  else PlutusTx.traceError "Odd number of outputs"
{-# INLINABLE checkScriptContext1 #-}

mkCheckScriptContext1Code :: ScriptContext -> PlutusTx.CompiledCode ()
mkCheckScriptContext1Code sc =
  let d = PlutusTx.toBuiltinData sc
  in
    $$(PlutusTx.compile [|| checkScriptContext1 ||])
    `PlutusTx.unsafeApplyCode`
    PlutusTx.liftCodeDef d

-- This example aims to *force* the decoding of the script context and then ignore it entirely.
-- This corresponds to the unfortunate case where the decoding "wrapper" around a script forces
-- all the decoding work to be done even if it isn't used.
checkScriptContext2 :: PlutusTx.BuiltinData -> ()
checkScriptContext2 d =
  let (sc :: ScriptContext) = PlutusTx.unsafeFromBuiltinData d
  -- Just using a bang pattern was not enough to stop GHC from getting
  -- rid of the dead binding before we even hit the plugin, this works
  -- for now!
  in case sc of
    !_ ->
      if 48 PlutusTx.* 9900 PlutusTx.== (475200 :: Integer)
      then ()
      else PlutusTx.traceError "Got my sums wrong"
{-# INLINABLE checkScriptContext2 #-}

mkCheckScriptContext2Code :: ScriptContext -> PlutusTx.CompiledCode ()
mkCheckScriptContext2Code sc =
  let d = PlutusTx.toBuiltinData sc
  in
    $$(PlutusTx.compile [|| checkScriptContext2 ||])
    `PlutusTx.unsafeApplyCode`
    PlutusTx.liftCodeDef d

{- Note [Redundant arguments to equality benchmarks]
The arguments for the benchmarks are passed as terms created with `liftCodeDef`.
But the benchmark still needs to _evaluate_ these terms, which adds overhead that
distracts from the main point.

We can't easily remove the overhead, but we can at least include it in both cases to
make things fairer. Hence we include redundant arguments in the two cases to ensure
the same work is done in both cases. There is a third case that is just this overhead
for comparison.
-}

-- This example checks the script context for equality (with itself) when encoded as `Data`.
-- That means it just takes a single builtin call, which is fast (so long as the builtin is
-- costed cheaply).
scriptContextEqualityData :: ScriptContext -> PlutusTx.BuiltinData -> ()
-- See Note [Redundant arguments to equality benchmarks]
scriptContextEqualityData _ d =
  if PlutusTx.equalsData d d
  then ()
  else PlutusTx.traceError "The argument is not equal to itself"
{-# INLINABLE scriptContextEqualityData #-}

mkScriptContextEqualityDataCode :: ScriptContext -> PlutusTx.CompiledCode ()
mkScriptContextEqualityDataCode sc =
  let d = PlutusTx.toBuiltinData sc
  in $$(PlutusTx.compile [|| scriptContextEqualityData ||])
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef sc
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef d

-- This example is just the overhead from the previous two
-- See Note [Redundant arguments to equality benchmarks]
scriptContextEqualityOverhead :: ScriptContext -> PlutusTx.BuiltinData -> ()
scriptContextEqualityOverhead _ _ = ()
{-# INLINABLE scriptContextEqualityOverhead #-}

mkScriptContextEqualityOverheadCode :: ScriptContext -> PlutusTx.CompiledCode ()
mkScriptContextEqualityOverheadCode sc =
  let d = PlutusTx.toBuiltinData sc
  in $$(PlutusTx.compile [|| scriptContextEqualityOverhead ||])
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef sc
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef d

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

-- The manually optimised version of a script which validates that the stake
-- credential is in the withdrawal map.
-- The "trick" is that, if it exists, there is a high probability of the stake
-- credential being either the first or the second element of the map.
forwardWithStakeTrickManual :: BuiltinData -> BuiltinData -> ()
forwardWithStakeTrickManual r_stake_cred r_ctx =
  let wdrl = getCtxWdrl r_ctx
      wdrlAtZero = BI.fst $ BI.head wdrl
      rest = BI.tail wdrl
      wdrlAtOne = BI.fst $ BI.head $ rest
   in if
        ( PlutusTx.equalsData r_stake_cred wdrlAtZero
        || PlutusTx.equalsData r_stake_cred wdrlAtOne
        )
        then ()
        else lookForCred rest
  where
    lookForCred :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) -> ()
    lookForCred =
      PlutusTx.caseList
        (\() -> PlutusTx.traceError "not found")
        (\p tl ->
          if PlutusTx.equalsData r_stake_cred (BI.fst p)
            then ()
            else lookForCred tl
        )
    getCtxWdrl :: BuiltinData -> BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
    getCtxWdrl d_ctx =
      BI.unsafeDataAsMap
      $ BI.head
      $ BI.tail
      $ BI.tail
      $ BI.tail
      $ BI.tail
      $ BI.tail
      $ BI.tail
      $ BI.snd
      $ BI.unsafeDataAsConstr
      $ BI.head
      $ BI.snd
      $ BI.unsafeDataAsConstr d_ctx
{-# INLINABLE forwardWithStakeTrickManual #-}

mkForwardWithStakeTrickManualCode
  :: StakingCredential
  -> ScriptContext
  -> PlutusTx.CompiledCode ()
mkForwardWithStakeTrickManualCode cred ctx =
  let c = PlutusTx.toBuiltinData cred
      sc = PlutusTx.toBuiltinData ctx
  in $$(PlutusTx.compile [|| forwardWithStakeTrickManual ||])
       `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef c
       `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef sc
