{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE EmptyDataDeriving   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-
Builtin contracts that are compiled together with the PAB.
-}
module Plutus.PAB.Effects.Contract.Builtin(
    Builtin
    , ContractConstraints
    , SomeBuiltin(..)
    , SomeBuiltinState(..)
    , BuiltinHandler(..)
    , handleBuiltin
    -- * Extracting schemas from contracts
    , type (.\\)
    , type (.\/)
    , EmptySchema
    , Empty
    , endpointsToSchemas
    , getResponse
    , fromResponse
    , HasDefinitions(..)
    ) where


import           Control.Monad                                    (unless)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error                        (Error, throwError)
import           Control.Monad.Freer.Extras.Log                   (LogMsg (..), logDebug)
import           Data.Aeson                                       (FromJSON, ToJSON, Value)
import qualified Data.Aeson                                       as JSON
import           Data.Foldable                                    (foldlM, traverse_)
import           Data.Row
import           GHC.Generics                                     (Generic)
import           Playground.Schema                                (endpointsToSchemas)
import           Playground.Types                                 (FunctionSchema)
import           Plutus.Contract                                  (ContractInstanceId, EmptySchema, IsContract (..))
import           Plutus.Contract.Effects                          (PABReq, PABResp)
import           Plutus.Contract.Resumable                        (Response, responses)
import           Plutus.Contract.Schema                           (Input, Output)
import           Plutus.Contract.State                            (ContractResponse (..), State (..))
import qualified Plutus.Contract.State                            as ContractState
import           Plutus.Contract.Types                            (ResumableResult (..), SuspendedContract (..))
import           Plutus.PAB.Core.ContractInstance.RequestHandlers (ContractInstanceMsg (ContractLog, ProcessFirstInboxMessage))
import           Plutus.PAB.Effects.Contract                      (ContractEffect (..), PABContract (..))
import           Plutus.PAB.Monitoring.PABLogMsg                  (PABMultiAgentMsg (..))
import           Plutus.PAB.Types                                 (PABError (..))
import           Plutus.Trace.Emulator.Types                      (ContractInstanceStateInternal (..))
import qualified Plutus.Trace.Emulator.Types                      as Emulator
import           Schema                                           (FormSchema)

-- | Contracts that are built into the PAB (ie. compiled with it) and receive
--   an initial value of type 'a'.
--
-- We have a dummy constructor so that we can convert this datatype in
-- Purescript with '(equal <*> (genericShow <*> mkSumType)) (Proxy @(Builtin A))'.
data Builtin a = Builtin deriving (Eq, Generic)

type ContractConstraints w schema error =
    ( Monoid w
    , Forall (Output schema) ToJSON
    , Forall (Input schema) ToJSON
    , Forall (Input schema) FromJSON
    , ToJSON error
    , ToJSON w
    , FromJSON w
    , AllUniqueLabels (Input schema)
    )

-- | Plutus contract with all parameters existentially quantified. Can be any contract that satisfies the
--   'ContractConstraints'.
data SomeBuiltin where
    SomeBuiltin
        :: forall contract w schema error a. (ContractConstraints w schema error, IsContract contract)
        => contract w schema error a -> SomeBuiltin

data SomeBuiltinState a where
    SomeBuiltinState ::
        forall a w schema error b.
        ContractConstraints w schema error
        => Emulator.ContractInstanceStateInternal w schema error b -- ^ Internal state
        -> w -- ^ Observable state (stored separately)
        -> SomeBuiltinState a

instance PABContract (Builtin a) where
    type ContractDef (Builtin a) = a
    type State (Builtin a) = SomeBuiltinState a
    serialisableState _ = getResponse

-- | Allows contract type `a` to specify its available contract definitions.
-- Also, for each contract type, we specify its contract function and its
-- schemas.
class HasDefinitions a where
    getDefinitions :: [a] -- ^ Available contract definitions for a contract type `a`
    getContract :: a -> SomeBuiltin -- ^ The actual contract function of contract type `a`
    getSchema :: a -> [FunctionSchema FormSchema] -- List of schemas for contract type `a`

-- | Defined in order to prevent type errors like: "Couldn't match type 'effs'
-- with 'effs1'".
newtype BuiltinHandler a = BuiltinHandler
    { contractHandler :: forall effs.
                         ( Member (Error PABError) effs
                         , Member (LogMsg (PABMultiAgentMsg (Builtin a))) effs
                         )
                      => ContractEffect (Builtin a) ~> Eff effs
    }

-- | Handle the 'ContractEffect' for a builtin contract type with parameter
--   @a@.
handleBuiltin :: HasDefinitions a => BuiltinHandler a
handleBuiltin = BuiltinHandler $ \case
    InitialState i c           -> case getContract c of SomeBuiltin c' -> initBuiltin i c'
    UpdateContract i _ state p -> case state of SomeBuiltinState s w -> updateBuiltin i s w p
    ExportSchema a             -> pure $ getSchema a

getResponse :: forall a. SomeBuiltinState a -> ContractResponse Value Value PABResp PABReq
getResponse (SomeBuiltinState s w) =
    ContractState.mapE JSON.toJSON
    $ ContractState.mapW JSON.toJSON
    $ ContractState.mkResponse w
    $ Emulator.instContractState
    $ Emulator.toInstanceState s

-- | Reconstruct a state from a serialised response by replaying back the
-- actions.
fromResponse :: forall a effs.
  ( Member (LogMsg (PABMultiAgentMsg (Builtin a))) effs
  , Member (Error PABError) effs
  )
  => ContractInstanceId
  -> SomeBuiltin
  -> ContractResponse Value Value PABResp PABReq
  -> Eff effs (SomeBuiltinState a)
fromResponse cid (SomeBuiltin contract) ContractResponse{newState=State{record}} = do
  initialState <- initBuiltinSilently @effs @a cid contract
  let runUpdate (SomeBuiltinState oldS oldW) n = do
          updateBuiltinSilently @effs @a cid oldS oldW (snd <$> n)
  foldlM runUpdate initialState (responses record)

initBuiltin, initBuiltinSilently ::
    forall effs a contract w schema error b.
    ( ContractConstraints w schema error
    , Member (LogMsg (PABMultiAgentMsg (Builtin a))) effs
    , IsContract contract
    )
    => ContractInstanceId
    -> contract w schema error b
    -> Eff effs (SomeBuiltinState a)
initBuiltin = initBuiltin' False
initBuiltinSilently = initBuiltin' True

initBuiltin' ::
    forall effs a contract w schema error b.
    ( ContractConstraints w schema error
    , Member (LogMsg (PABMultiAgentMsg (Builtin a))) effs
    , IsContract contract
    )
    => Bool -- ^ If True, log new messages, otherwise stay silent.
    -> ContractInstanceId
    -> contract w schema error b
    -> Eff effs (SomeBuiltinState a)
initBuiltin' silent i con = do
    let initialState = Emulator.emptyInstanceState (toContract con)
    unless silent $ logNewMessages @a i initialState
    pure $ SomeBuiltinState initialState mempty

updateBuiltin, updateBuiltinSilently ::
    forall effs a w schema error b.
    ( ContractConstraints w schema error
    , Member (Error PABError) effs
    , Member (LogMsg (PABMultiAgentMsg (Builtin a))) effs
    )
    => ContractInstanceId
    -> Emulator.ContractInstanceStateInternal w schema error b
    -> w
    -> Response PABResp
    -> Eff effs (SomeBuiltinState a)
updateBuiltin = updateBuiltin' False
updateBuiltinSilently = updateBuiltin' True

updateBuiltin' ::
    forall effs a w schema error b.
    ( ContractConstraints w schema error
    , Member (Error PABError) effs
    , Member (LogMsg (PABMultiAgentMsg (Builtin a))) effs
    )
    => Bool
    -> ContractInstanceId
    -> Emulator.ContractInstanceStateInternal w schema error b
    -> w
    -> Response PABResp
    -> Eff effs (SomeBuiltinState a)
updateBuiltin' silent i oldState oldW resp = do
    let newState = Emulator.addEventInstanceState resp oldState
    case newState of
        Just k -> do
            logDebug @(PABMultiAgentMsg (Builtin a)) (ContractInstanceLog $ ProcessFirstInboxMessage i resp)
            unless silent $ logNewMessages @a i k
            let newW = oldW <> (_lastState $ _resumableResult $ Emulator.cisiSuspState oldState)
            pure (SomeBuiltinState k newW)
        _      -> throwError $ ContractCommandError 0 "failed to update contract"

logNewMessages ::
    forall b w s e a effs.
    ( Member (LogMsg (PABMultiAgentMsg (Builtin b))) effs
    )
    => ContractInstanceId
    -> ContractInstanceStateInternal w s e a
    -> Eff effs ()
logNewMessages i ContractInstanceStateInternal{cisiSuspState=SuspendedContract{_resumableResult=ResumableResult{_lastLogs, _observableState}}} = do
    traverse_ (send @(LogMsg (PABMultiAgentMsg (Builtin b))) . LMessage . fmap (ContractInstanceLog . ContractLog i)) _lastLogs
