
-- editorconfig-checker-disable-file


-----------------------------------------------------------------------------
--
-- Module      :  $Headers
-- License     :  Apache 2.0
--
-- Stability   :  Experimental
-- Portability :  Portable
--
-- | Marlowe validators.
--
-----------------------------------------------------------------------------


{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}

{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.0.0 #-}

module PlutusBenchmark.Marlowe.Scripts.Semantics
  ( -- * Types
    MarloweInput
  , MarloweTxInput(..)
    -- * Semantics Validator
  , marloweValidatorHash
  , marloweValidatorBytes
  , marloweValidator
  , mkMarloweValidator
    -- * Utilities
  , marloweTxInputsFromInputs
  ) where


import GHC.Generics (Generic)
import PlutusBenchmark.Marlowe.Core.V1.Semantics as Semantics (MarloweData (..),
                                                               MarloweParams (MarloweParams, rolesCurrency),
                                                               Payment,
                                                               TransactionError (TEAmbiguousTimeIntervalError, TEApplyNoMatchError, TEHashMismatch, TEIntervalError, TEUselessTransaction),
                                                               TransactionInput (TransactionInput, txInputs, txInterval),
                                                               TransactionOutput (Error, TransactionOutput, txOutContract, txOutPayments, txOutState),
                                                               computeTransaction, pattern Payment,
                                                               totalBalance)
import PlutusBenchmark.Marlowe.Core.V1.Semantics.Types
import PlutusBenchmark.Marlowe.Scripts.RolePayout (rolePayoutValidatorHash)
import PlutusLedgerApi.V2 (Credential (..), Datum (Datum), DatumHash (DatumHash), Extended (..),
                           Interval (..), LowerBound (..), POSIXTime (..), POSIXTimeRange,
                           ScriptContext (ScriptContext, scriptContextPurpose, scriptContextTxInfo),
                           ScriptHash (..), ScriptPurpose (Spending), SerialisedScript,
                           TxInInfo (TxInInfo, txInInfoOutRef, txInInfoResolved),
                           TxInfo (TxInfo, txInfoInputs, txInfoOutputs, txInfoValidRange),
                           UpperBound (..), serialiseCompiledCode)
import PlutusLedgerApi.V2.Contexts (findDatum, findDatumHash, txSignedBy, valueSpent)
import PlutusLedgerApi.V2.Tx (OutputDatum (OutputDatumHash),
                              TxOut (TxOut, txOutAddress, txOutDatum, txOutValue))
import PlutusTx (CompiledCode, makeIsDataIndexed, makeLift, unsafeFromBuiltinData)
import PlutusTx.Plugin ()
import PlutusTx.Prelude as PlutusTxPrelude (AdditiveGroup ((-)), AdditiveMonoid (zero),
                                            AdditiveSemigroup ((+)), Bool (..), BuiltinByteString,
                                            BuiltinData, BuiltinString, Enum (fromEnum), Eq (..),
                                            Functor (fmap), Integer, Maybe (..), Ord ((>)),
                                            Semigroup ((<>)), all, any, check, elem, filter, find,
                                            foldMap, id, null, otherwise, snd, toBuiltin, ($), (&&),
                                            (.), (/=), (||))

import Cardano.Crypto.Hash qualified as Hash
import Data.ByteString qualified as BS
import Data.ByteString.Short qualified as SBS
import PlutusCore.Version (plcVersion100)
import PlutusLedgerApi.V1.Address qualified as Address (scriptHashAddress)
import PlutusLedgerApi.V1.DataValue qualified as Data
import PlutusLedgerApi.V1.DataValue qualified as DataValue
import PlutusLedgerApi.V1.Value qualified as SOP
import PlutusLedgerApi.V2 qualified as Ledger (Address (Address))
import PlutusTx qualified
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.DataList qualified as Data
import PlutusTx.DataList qualified as DataList
import PlutusTx.DataMap qualified as Data
import PlutusTx.DataMap qualified as DataMap
import PlutusTx.DataPair (DataElem)
import PlutusTx.DataPair qualified as Data
import PlutusTx.DataPair qualified as DataPair
import PlutusTx.Trace (traceError, traceIfFalse)
import Prelude qualified as Haskell


-- | Input to a Marlowe transaction.
type MarloweInput = [MarloweTxInput]


-- | Tag for the Marlowe semantics validator.
data TypedMarloweValidator


-- | A single input applied in the Marlowe semantics validator.
data MarloweTxInput = Input InputContent
                    | MerkleizedTxInput InputContent BuiltinByteString
  deriving stock (Haskell.Show,Haskell.Eq,Generic)


{-# INLINABLE closeInterval #-}
-- | Convert a Plutus POSIX time range into the closed interval needed by Marlowe semantics.
closeInterval :: POSIXTimeRange -> Maybe (POSIXTime, POSIXTime)
closeInterval (Interval (LowerBound (Finite (POSIXTime l)) lc) (UpperBound (Finite (POSIXTime h)) hc)) =
  Just
    (
      POSIXTime $ l + 1 - fromEnum lc  -- Add one millisecond if the interval was open.
    , POSIXTime $ h - 1 + fromEnum hc  -- Subtract one millisecond if the interval was open.
    )
closeInterval _ = Nothing

-- TODO: abstract away
toDataValue :: SOP.Value -> Data.Value
toDataValue = PlutusTx.unsafeFromBuiltinData . PlutusTx.toBuiltinData

toDataCurrencySymbol :: SOP.CurrencySymbol -> Data.CurrencySymbol
toDataCurrencySymbol = PlutusTx.unsafeFromBuiltinData . PlutusTx.toBuiltinData

toDataTokenName :: SOP.TokenName -> Data.TokenName
toDataTokenName = PlutusTx.unsafeFromBuiltinData . PlutusTx.toBuiltinData

{-# INLINABLE mkMarloweValidator #-}
-- | The Marlowe semantics validator.
mkMarloweValidator
    :: ScriptHash     -- ^ The hash of the corresponding Marlowe payout validator.
    -> MarloweData    -- ^ The datum is the Marlowe parameters, state, and contract.
    -> MarloweInput   -- ^ The redeemer is the list of inputs applied to the contract.
    -> ScriptContext  -- ^ The script context.
    -> Bool           -- ^ Whether the transaction validated.
mkMarloweValidator
    rolePayoutValidatorHash
    MarloweData{..}
    marloweTxInputs
    ctx@ScriptContext{scriptContextTxInfo} = do

    let scriptInValue = toDataValue $ txOutValue $ txInInfoResolved ownInput
    let interval =
            -- Marlowe semantics require a closed interval, so we might adjust by one millisecond.
            case closeInterval $ txInfoValidRange scriptContextTxInfo of
                Just interval' -> interval'
                Nothing        -> traceError "a"

    -- Find Contract continuation in TxInfo datums by hash or fail with error.
    let inputs = fmap marloweTxInputToInput marloweTxInputs

    {-  We do not check that a transaction contains exact input payments.
        We only require an evidence from a party, e.g. a signature for PubKey party,
        or a spend of a 'party role' token.  This gives huge flexibility by allowing
        parties to provide multiple inputs (either other contracts or P2PKH).
        Then, we check scriptOutput to be correct.
     -}
    let inputContents = fmap getInputContent inputs

    -- Check that the required signatures and role tokens are present.
    -- [Marlowe-Cardano Specification: "Constraint 14. Inputs authorized".]
    let inputsOk = allInputsAreAuthorized inputContents

    -- [Marlowe-Cardano Specification: "Constraint 5. Input value from script".]
    -- [Marlowe-Cardano Specification: "Constraint 13. Positive balances".]
    -- [Marlowe-Cardano Specification: "Constraint 19. No duplicates".]
    -- Check that the initial state obeys the Semantic's invariants.
    let preconditionsOk = checkState "i" scriptInValue marloweState

    -- [Marlowe-Cardano Specification: "Constraint 0. Input to semantics".]
    -- Package the inputs to be applied in the semantics.
    let txInput = TransactionInput {
            txInterval = interval,
            txInputs = inputs }

    -- [Marlowe-Cardano Specification: "Constraint 7. Input state".]
    -- [Marlowe-Cardano Specification: "Constraint 8. Input contract".]
    -- The semantics computation operates on the state and contract from
    -- the incoming datum.
    let computedResult = computeTransaction txInput marloweState marloweContract
    case computedResult of
        TransactionOutput {txOutPayments, txOutState, txOutContract} -> do

            -- [Marlowe-Cardano Specification: "Constraint 9. Marlowe parameters".]
            -- [Marlowe-Cardano Specification: "Constraint 10. Output state".]
            -- [Marlowe-Cardano Specification: "Constraint 11. Output contract."]
            -- The output datum maintains the parameters and uses the state
            -- and contract resulting from the semantics computation.
            let marloweData = MarloweData {
                    marloweParams = marloweParams,
                    marloweContract = txOutContract,
                    marloweState = txOutState }

                -- Each party must receive as least as much value as the semantics specify.
                -- [Marlowe-Cardano Specification: "Constraint 15. Sufficient payment."]
                payoutsByParty = DataList.foldMap payoutByParty (DataList.fromSOP txOutPayments)
                payoutsOk = payoutConstraints payoutsByParty

                checkContinuation = case txOutContract of
                    -- [Marlowe-Cardano Specification: "Constraint 4. No output to script on close".]
                    Close -> traceIfFalse "c" hasNoOutputToOwnScript
                    _ -> let
                        totalIncome = foldMap collectDeposits inputContents
                        totalPayouts = DataMap.foldMap id payoutsByParty
                        finalBalance = scriptInValue + totalIncome - totalPayouts
                        in
                             -- [Marlowe-Cardano Specification: "Constraint 3. Single Marlowe output".]
                             -- [Marlowe-Cardano Specification: "Constraint 6. Output value to script."]
                             -- Check that the single Marlowe output has the correct datum and value.
                             checkOwnOutputConstraint marloweData finalBalance
                             -- [Marlowe-Cardano Specification: "Constraint 18. Final balance."]
                             -- [Marlowe-Cardano Specification: "Constraint 13. Positive balances".]
                             -- [Marlowe-Cardano Specification: "Constraint 19. No duplicates".]
                             -- Check that the final state obeys the Semantic's invariants.
                          && checkState "o" finalBalance txOutState
            preconditionsOk && inputsOk && payoutsOk && checkContinuation
              -- [Marlowe-Cardano Specification: "20. Single satsifaction".]
              -- Either there must be no payouts, or there must be no other validators.
              && traceIfFalse "z" (DataMap.null payoutsByParty || noOthers)
        Error TEAmbiguousTimeIntervalError -> traceError "i"
        Error TEApplyNoMatchError -> traceError "n"
        Error (TEIntervalError (InvalidInterval _)) -> traceError "j"
        Error (TEIntervalError (IntervalInPastError _ _)) -> traceError "k"
        Error TEUselessTransaction -> traceError "u"
        Error TEHashMismatch -> traceError "m"

  where

    -- The roles currency is in the Marlowe parameters.
    MarloweParams{ rolesCurrency } = marloweParams

    -- Find the input being spent by a script.
    findOwnInput :: ScriptContext -> Maybe TxInInfo
    findOwnInput ScriptContext{scriptContextTxInfo=TxInfo{txInfoInputs}, scriptContextPurpose=Spending txOutRef} =
        find (\TxInInfo{txInInfoOutRef} -> txInInfoOutRef == txOutRef) txInfoInputs
    findOwnInput _ = Nothing

    -- [Marlowe-Cardano Specification: "2. Single Marlowe script input".]
    -- The inputs being spent by this script, and whether other validators are present.
    ownInput :: TxInInfo
    noOthers :: Bool
    (ownInput@TxInInfo{txInInfoResolved=TxOut{txOutAddress=ownAddress}}, noOthers) =
        case findOwnInput ctx of
            Just ownTxInInfo -> examineScripts (sameValidatorHash ownTxInInfo) Nothing True (txInfoInputs scriptContextTxInfo)
            _ -> traceError "x" -- Input to be validated was not found.

    -- Check for the presence of multiple Marlowe validators or other Plutus validators.
    examineScripts
      :: (ScriptHash -> Bool)  -- Test for this validator.
      -> Maybe TxInInfo           -- The input for this validator, if found so far.
      -> Bool                     -- Whether no other validator has been found so far.
      -> [TxInInfo]               -- The inputs remaining to be examined.
      -> (TxInInfo, Bool)         -- The input for this validator and whehter no other validators are present.
    -- This validator has not been found.
    examineScripts _ Nothing _ [] = traceError "x"
    -- This validator has been found, and other validators may have been found.
    examineScripts _ (Just self) noOthers [] = (self, noOthers)
    -- Found both this validator and another script, so we short-cut.
    examineScripts _ (Just self) False _ = (self, False)
     -- Found one script.
    examineScripts f mSelf noOthers (tx@TxInInfo{txInInfoResolved=TxOut{txOutAddress=Ledger.Address (ScriptCredential vh) _}} : txs)
      -- The script is this validator.
      | f vh = case mSelf of
                 -- We hadn't found it before, so we save it in `mSelf`.
                 Nothing -> examineScripts f (Just tx) noOthers txs
                 -- We already had found this validator before
                 Just _  -> traceError "w"
      -- The script is something else, so we set `noOther` to `False`.
      | otherwise = examineScripts f mSelf False txs
    -- An input without a validator is encountered.
    examineScripts f self others (_ : txs) = examineScripts f self others txs

    -- Check if inputs are being spent from the same script.
    sameValidatorHash:: TxInInfo -> ScriptHash -> Bool
    sameValidatorHash TxInInfo{txInInfoResolved=TxOut{txOutAddress=Ledger.Address (ScriptCredential vh1) _}} vh2 = vh1 == vh2
    sameValidatorHash _ _ = False

    -- Check a state for the correct value, positive accounts, and no duplicates.
    checkState :: BuiltinString -> Data.Value -> State -> Bool
    checkState tag expected State{..} =
      let
        positiveBalance :: Integer -> Bool
        positiveBalance balance = balance > 0
        noDuplicates :: (DataElem k, DataElem v, Eq k) => Data.Map k v -> Bool
        noDuplicates am =
          let
            test DataList.Nil = True           -- An empty list has no duplicates.
            test (DataList.Cons x xs)            -- Look for a duplicate of the head in the tail.
              | DataList.elem x xs = False    -- A duplicate is present.
              | otherwise = test xs  -- Continue searching for a duplicate.
          in
            test $ DataMap.keys am
      in
           -- [Marlowe-Cardano Specification: "Constraint 5. Input value from script".]
           -- and/or
           -- [Marlowe-Cardano Specification: "Constraint 18. Final balance."]
           traceIfFalse ("v"  <> tag) (totalBalance accounts == expected)
           -- [Marlowe-Cardano Specification: "Constraint 13. Positive balances".]
        && traceIfFalse ("b"  <> tag) (DataMap.all positiveBalance accounts)
           -- [Marlowe-Cardano Specification: "Constraint 19. No duplicates".]
        && traceIfFalse ("ea" <> tag) (noDuplicates accounts)
        && traceIfFalse ("ec" <> tag) (noDuplicates choices)
        && traceIfFalse ("eb" <> tag) (noDuplicates boundValues)

    -- Look up the Datum hash for specific data.
    findDatumHash' :: PlutusTx.ToData o => o -> Maybe DatumHash
    findDatumHash' datum = findDatumHash (Datum $ PlutusTx.toBuiltinData datum) scriptContextTxInfo

    -- Check that the correct datum and value is being output to the script.
    checkOwnOutputConstraint :: MarloweData -> Data.Value -> Bool
    checkOwnOutputConstraint ocDatum ocValue =
        let hsh = findDatumHash' ocDatum
        in traceIfFalse "d" -- "Output constraint"
        $ checkScriptOutput (==) ownAddress hsh ocValue getContinuingOutput

    getContinuingOutput :: TxOut
    ~getContinuingOutput = case filter (\TxOut{txOutAddress} -> ownAddress == txOutAddress) allOutputs of
        [out] -> out
        _     -> traceError "o" -- No continuation or multiple Marlowe contract outputs is forbidden.

    -- Check that address, value, and datum match the specified.
    checkScriptOutput :: (Data.Value -> Data.Value -> Bool) -> Ledger.Address -> Maybe DatumHash -> Data.Value -> TxOut -> Bool
    checkScriptOutput comparison addr hsh value TxOut{txOutAddress, txOutValue, txOutDatum=OutputDatumHash svh} =
                    toDataValue txOutValue `comparison` value && hsh == Just svh && txOutAddress == addr
    checkScriptOutput _ _ _ _ _ = False

    -- Check for any output to the script address.
    hasNoOutputToOwnScript :: Bool
    hasNoOutputToOwnScript = all ((/= ownAddress) . txOutAddress) allOutputs

    -- All of the script outputs.
    allOutputs :: [TxOut]
    allOutputs = txInfoOutputs scriptContextTxInfo

    -- Check mekleization and transform transaction input to semantics input.
    marloweTxInputToInput :: MarloweTxInput -> Input
    marloweTxInputToInput (MerkleizedTxInput input hash) =
        case findDatum (DatumHash hash) scriptContextTxInfo of
            Just (Datum d) -> let
                continuation = PlutusTx.unsafeFromBuiltinData d
                in MerkleizedInput input hash continuation
            Nothing -> traceError "h"
    marloweTxInputToInput (Input input) = NormalInput input

    -- Check that inputs are authorized.
    allInputsAreAuthorized :: [InputContent] -> Bool
    allInputsAreAuthorized = all validateInputWitness
      where
        validateInputWitness :: InputContent -> Bool
        validateInputWitness input =
            case input of
                IDeposit _ party _ _         -> validatePartyWitness party  -- The party must witness a deposit.
                IChoice (ChoiceId _ party) _ -> validatePartyWitness party  -- The party must witness a choice.
                INotify                      -> True                        -- No witness is needed for a notify.
          where
            validatePartyWitness :: Party -> Bool
            validatePartyWitness (Address _ address) = traceIfFalse "s" $ txSignedByAddress address  -- The key must have signed.
            validatePartyWitness (Role role)         =
              traceIfFalse "t"                              -- The role token must be present.
              $ DataValue.singleton (toDataCurrencySymbol rolesCurrency) (toDataTokenName role) 1
              `DataValue.leq` (toDataValue $ valueSpent scriptContextTxInfo)

    -- Tally the deposits in the input.
    collectDeposits :: InputContent -> Data.Value
    collectDeposits (IDeposit _ _ (Token cur tok) amount)
      | amount > 0    = DataValue.singleton cur tok amount  -- SCP-5123: Semantically negative deposits
      | otherwise     = zero                          -- do not remove funds from the script's UTxO.
    collectDeposits _ = zero

    -- Extract the payout to a party.
    payoutByParty :: Payment -> Data.Map Party Data.Value
    payoutByParty (Payment _ (Party party) (Token cur tok) amount)
      | amount > 0 = DataMap.singleton party $ DataValue.singleton cur tok amount
      | otherwise  = DataMap.empty  -- NOTE: Perhaps required because semantics may make zero payments
                                     -- (though this passes the test suite), but removing this function's
                                     -- guard reduces the validator size by 20 bytes.
    payoutByParty (Payment _ (Account _) _ _ )       = DataMap.empty

    -- Check outgoing payments.
    payoutConstraints :: Data.Map Party Data.Value-> Bool
    payoutConstraints = DataMap.allPair payoutToTxOut
      where
        payoutToTxOut :: Data.Pair Party Data.Value -> Bool
        payoutToTxOut (Data.Pair party value) = case party of
            -- [Marlowe-Cardano Specification: "Constraint 15. Sufficient Payment".]
            -- SCP-5128: Note that the payment to an address may be split into several outputs but the payment to a role must be
            -- a single output. The flexibily of multiple outputs accommodates wallet-related practicalities such as the change and
            -- the return of the role token being in separate UTxOs in situations where a contract is also paying to the address
            -- where that change and that role token are sent.
            Address _ address  -> traceIfFalse "p" $ value `DataValue.leq` valuePaidToAddress address  -- At least sufficient value paid.
            Role role -> let
                hsh = findDatumHash' (rolesCurrency, role)
                addr = Address.scriptHashAddress rolePayoutValidatorHash
                -- Some output must have the correct value and datum to the role-payout address.
                in traceIfFalse "r" $ any (checkScriptOutput DataValue.geq addr hsh value) allOutputs

    -- The key for the address must have signed.
    txSignedByAddress :: Ledger.Address -> Bool
    txSignedByAddress (Ledger.Address (PubKeyCredential pkh) _) = scriptContextTxInfo `txSignedBy` pkh
    txSignedByAddress _                                         = False

    -- Tally the value paid to an address.
    valuePaidToAddress :: Ledger.Address -> Data.Value
    valuePaidToAddress address = foldMap (toDataValue . txOutValue) $ filter ((== address) . txOutAddress) allOutputs


-- | Convert semantics input to transaction input.
marloweTxInputFromInput :: Input -> MarloweTxInput
marloweTxInputFromInput (NormalInput i)         = Input i
marloweTxInputFromInput (MerkleizedInput i h _) = MerkleizedTxInput i h


-- | Convert semantics inputs to transaction inputs.
marloweTxInputsFromInputs :: [Input] -> [MarloweTxInput]
marloweTxInputsFromInputs = fmap marloweTxInputFromInput


-- Lifting data types to Plutus Core
makeLift ''MarloweTxInput
makeIsDataIndexed ''MarloweTxInput [('Input,0),('MerkleizedTxInput,1)]


-- | Compute the hash of a script.
hashScript :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ()) -> ScriptHash
hashScript =
  -- FIXME: Apparently this is the wrong recipe, since its hash disagrees with `cardano-cli`.
  ScriptHash
    . toBuiltin
    . (Hash.hashToBytes :: Hash.Hash Hash.Blake2b_224 SBS.ShortByteString -> BS.ByteString)
    . Hash.hashWith (BS.append "\x02" . SBS.fromShort)  -- For Plutus V2.
    . serialiseCompiledCode


-- | The validator for Marlowe semantics.
marloweValidator :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
marloweValidator =
  let
    marloweValidator' :: ScriptHash -> BuiltinData -> BuiltinData -> BuiltinData -> ()
    marloweValidator' rpvh d r p =
      check
        $ mkMarloweValidator rpvh
            (unsafeFromBuiltinData d)
            (unsafeFromBuiltinData r)
            (unsafeFromBuiltinData p)

    errorOrApplied =
      $$(PlutusTx.compile [|| marloweValidator' ||])
        `PlutusTx.applyCode` PlutusTx.liftCode plcVersion100 rolePayoutValidatorHash
  in
    case errorOrApplied of
      Haskell.Left err ->
        Haskell.error $ "Application of role-payout validator hash to marlowe validator failed."
          <> err
      Haskell.Right applied -> applied


-- | The serialisation of the Marlowe semantics validator.
marloweValidatorBytes :: SerialisedScript
marloweValidatorBytes = serialiseCompiledCode marloweValidator


-- | The hash of the Marlowe semantics validator.
marloweValidatorHash :: ScriptHash
marloweValidatorHash = hashScript marloweValidator
