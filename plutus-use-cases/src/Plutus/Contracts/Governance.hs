{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
module Plutus.Contracts.Governance (
      contract
    , scriptInstance
    , client
    , mkTokenName
    , mkValidator
    , votingValue
    , Proposal(..)
    , Voting(..)
    , GovState(..)
    , GovError
    , Params(..)
    , Schema
    ) where

import           Control.Lens                 (makeClassyPrisms, review)
import           Control.Monad
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Semigroup               (Sum (..))
import           Data.String                  (fromString)
-- import qualified Data.Text                    as T
-- import qualified Data.Text.Encoding           as E
import           GHC.Generics                 (Generic)
import           Ledger                       (MonetaryPolicyHash, PubKeyHash, Slot (..), TokenName)
import           Ledger.Constraints           (TxConstraints)
import qualified Ledger.Constraints           as Constraints
import qualified Ledger.Typed.Scripts         as Scripts
import qualified Ledger.Value                 as Value
import           Plutus.Contract
import           Plutus.Contract.StateMachine (AsSMContractError, State (..), StateMachine (..), Void)
import qualified Plutus.Contract.StateMachine as SM
import qualified PlutusTx
import qualified PlutusTx.AssocMap            as AssocMap
import           PlutusTx.Prelude
import qualified Prelude


data Proposal = Proposal
    { votingDeadline :: Slot -- TODO: not used yet
    , newLaw         :: ByteString
    , tokenName      :: TokenName
    }
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data Voting = Voting
    { proposal :: Proposal
    , votes    :: AssocMap.Map TokenName Bool
    }
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data GovState = GovState
    { law    :: ByteString
    , mph    :: MonetaryPolicyHash
    , voting :: Maybe Voting
    }
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data GovInput
    = ForgeTokens [TokenName]
    | ProposeChange Proposal
    | AddVote TokenName Bool
    | FinishVoting
    | CancelVoting
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

type Schema =
    BlockchainActions
        .\/ Endpoint "new-law" ByteString
        .\/ Endpoint "propose-change" Proposal
        .\/ Endpoint "add-vote" (TokenName, Bool)
        .\/ Endpoint "finish-voting" ()
        .\/ Endpoint "cancel-voting" ()

data Params = Params
    { initialHolders :: [PubKeyHash]
    , requiredVotes  :: Integer
    , baseTokenName  :: TokenName
    }


data GovError =
    GovContractError ContractError
    | GovStateMachineError SM.SMContractError
    deriving stock (Prelude.Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

makeClassyPrisms ''GovError

instance AsContractError GovError where
    _ContractError = _GovContractError

instance AsSMContractError GovError where
    _SMContractError = _GovStateMachineError

type GovernanceMachine = StateMachine GovState GovInput

{-# INLINABLE machine #-}
machine :: Params -> GovernanceMachine
machine params = SM.mkStateMachine (transition params) isFinal where
    {-# INLINABLE isFinal #-}
    isFinal _ = False

{-# INLINABLE mkValidator #-}
mkValidator :: Params -> Scripts.ValidatorType GovernanceMachine
mkValidator params = SM.mkValidator $ machine params

scriptInstance :: Params -> Scripts.ScriptInstance GovernanceMachine
scriptInstance = Scripts.validatorParam @GovernanceMachine
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator

client :: Params -> SM.StateMachineClient GovState GovInput
client params = SM.mkStateMachineClient $ SM.StateMachineInstance (machine params) (scriptInstance params)

mkTokenName :: TokenName -> Integer -> TokenName
mkTokenName base ix = fromString (Value.toString base ++ show ix)

{-# INLINABLE votingValue #-}
votingValue :: MonetaryPolicyHash -> TokenName -> Value.Value
votingValue mph tokenName =
    Value.singleton (Value.mpsSymbol mph) tokenName 1

{-# INLINABLE ownsVotingToken #-}
ownsVotingToken :: MonetaryPolicyHash -> TokenName -> TxConstraints Void Void
ownsVotingToken mph tokenName = mempty -- TODO

{-# INLINABLE transition #-}
transition :: Params -> State GovState -> GovInput -> Maybe (TxConstraints Void Void, State GovState)
transition Params{..} State{ stateData = s, stateValue = currentValue} i = case (s, i) of

    (GovState{mph}, ForgeTokens tokenNames) ->
        let (total, constraints) = foldMap
                (\(pk, nm) -> let v = votingValue mph nm in (v, Constraints.mustPayToPubKey pk v))
                (zip initialHolders tokenNames)
        in Just (constraints <> Constraints.mustForgeValue total, State s currentValue)

    (GovState law mph Nothing, ProposeChange proposal) ->
        Just (ownsVotingToken mph (tokenName proposal), State (GovState law mph (Just (Voting proposal AssocMap.empty))) currentValue)

    (GovState law mph (Just (Voting p oldMap)), AddVote tokenName vote) ->
        let newMap = AssocMap.insert tokenName vote oldMap
            constraints = ownsVotingToken mph tokenName
        in Just (constraints, State (GovState law mph (Just (Voting p newMap))) currentValue)

    (GovState oldLaw mph (Just (Voting Proposal{newLaw} votes)), FinishVoting) ->
        let (Sum ayes, Sum nays) = foldMap (\b -> if b then (Sum 1, Sum 0) else (Sum 0, Sum 1)) votes
        in if ayes >= requiredVotes -- Enough votes in favor
            then Just (mempty, State (GovState newLaw mph Nothing) currentValue)
            else if nays > length initialHolders - requiredVotes -- Enough opposed votes
                then Just (mempty, State (GovState oldLaw mph Nothing) currentValue)
                else Nothing -- Not enough votes either way, use cancel-voting to cancel

    (GovState law mph (Just _), CancelVoting) ->
        Just (mempty, State (GovState law mph Nothing) currentValue)

    _ -> Nothing


contract ::
    AsGovError e
    => Params
    -> Contract () Schema e ()
contract params = forever $ mapError (review _GovError) endpoints where
    theClient = client params
    endpoints = initLaw `select` propose `select` finish `select` cancel `select` addVote
    propose = endpoint @"propose-change" >>= SM.runStep theClient . ProposeChange
    finish  = endpoint @"finish-voting" >> SM.runStep theClient FinishVoting
    cancel  = endpoint @"cancel-voting" >> SM.runStep theClient CancelVoting
    addVote = do
        (tokenName, vote) <- endpoint @"add-vote"
        SM.runStep theClient (AddVote tokenName vote)
    initLaw = do
        bsLaw <- endpoint @"new-law"
        let mph = Scripts.monetaryPolicyHash (scriptInstance params)
        void $ SM.runInitialise theClient (GovState bsLaw mph Nothing) mempty
        let tokens = zipWith (const (mkTokenName (baseTokenName params))) (initialHolders params) [1..]
        SM.runStep theClient $ ForgeTokens tokens

PlutusTx.makeLift ''Params
PlutusTx.unstableMakeIsData ''Proposal
PlutusTx.makeLift ''Proposal
PlutusTx.unstableMakeIsData ''Voting
PlutusTx.makeLift ''Voting
PlutusTx.unstableMakeIsData ''GovState
PlutusTx.makeLift ''GovState
PlutusTx.unstableMakeIsData ''GovInput
PlutusTx.makeLift ''GovInput
