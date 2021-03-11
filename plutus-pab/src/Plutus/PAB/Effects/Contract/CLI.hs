{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
{-

'ContractEffect' handler for contracts that use the CLI
interface (see 'Plutus.PAB.ContractCLI').

-}
-- FIXME: Plutus.PAB.Effects.Contract.ContractExe
module Plutus.PAB.Effects.Contract.CLI(
    ContractExe(..)
    , handleContractEffectContractExe
    , ContractExeLogMsg(..)
    ) where

import           Cardano.BM.Data.Tracer                  (ToObject (..), TracingVerbosity (..))
import           Cardano.BM.Data.Tracer.Extras           (StructuredLog (..), Tagged (..), mkObjectStr)
import           Control.Monad.Freer                     (Eff, LastMember, Member, sendM, type (~>))
import           Control.Monad.Freer.Error               (Error, throwError)
import           Control.Monad.Freer.Extras.Log          (LogMsg, logDebug)
import           Control.Monad.IO.Class                  (MonadIO (..))
import           Data.Aeson                              (FromJSON (..), ToJSON (..), Value)
import qualified Data.Aeson                              as JSON
import qualified Data.Aeson.Encode.Pretty                as JSON
import qualified Data.ByteString.Lazy.Char8              as BSL8
import qualified Data.HashMap.Strict                     as HM
import           Data.String                             (IsString (..))
import           Data.Text                               (Text)
import qualified Data.Text                               as Text
import           Data.Text.Prettyprint.Doc               (Pretty, hang, pretty, viaShow, vsep, (<+>))
import           GHC.Generics                            (Generic)
import           Plutus.Contract.Resumable      (Response)
import           Plutus.Contract.State          (ContractRequest (..))
import           Plutus.PAB.Effects.Contract             (ContractEffect (..), PABContract (..))
import           Plutus.PAB.Events.Contract              (ContractPABRequest)
import qualified Plutus.PAB.Events.Contract              as Events.Contract
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import qualified Plutus.PAB.Events.ContractInstanceState as ContractInstanceState
import           Plutus.PAB.Types                        (PABError (ContractCommandError))
import           System.Exit                             (ExitCode (ExitFailure, ExitSuccess))
import           System.Process                          (readProcessWithExitCode)

instance PABContract ContractExe where
    type ContractDef ContractExe = ContractExe
    type State ContractExe = PartiallyDecodedResponse ContractPABRequest

    requests = error "FIXME"

newtype ContractExe =
    ContractExe
        { contractPath :: FilePath
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance StructuredLog ContractExe where
    toStructuredLog e = HM.singleton "contract" (toJSON e)

instance Pretty ContractExe where
    pretty ContractExe {contractPath} = "Path:" <+> pretty contractPath

-- | Handle 'ContractEffect ContractExe' by making calls to compiled contract
--   executables
handleContractEffectContractExe ::
       ( Member (LogMsg ContractExeLogMsg) effs
       , Member (Error PABError) effs
       , LastMember m effs
       , MonadIO m)
    => ContractEffect ContractExe
    ~> Eff effs
handleContractEffectContractExe =
    \case
        InitialState (ContractExe contractPath) -> do
            logDebug $ InitContractMsg contractPath
            liftProcess $ readProcessWithExitCode contractPath ["init"] ""
        UpdateContract (ContractExe contractPath) (oldState :: PartiallyDecodedResponse ContractPABRequest) (input :: Response Events.Contract.ContractResponse) -> do
            let req :: ContractRequest Value
                req = ContractRequest{oldState = ContractInstanceState.newState oldState, event = toJSON <$> input}
                pl = BSL8.unpack (JSON.encodePretty req)
            logDebug $ UpdateContractMsg contractPath req
            liftProcess $ readProcessWithExitCode contractPath ["update"] pl
        -- InvokeContract contractCommand -> do
        --     logDebug InvokeContractMsg
        --     case contractCommand of
        --         InitContract (ContractExe contractPath) -> do
        --             logDebug $ InitContractMsg contractPath
        --             liftProcess $ readProcessWithExitCode contractPath ["init"] ""
        --         UpdateContract (ContractExe contractPath) payload -> do
        --             let pl = BSL8.unpack (JSON.encodePretty payload)
        --             logDebug $ UpdateContractMsg contractPath payload
        --             liftProcess $ readProcessWithExitCode contractPath ["update"] pl
        ExportSchema (ContractExe contractPath) -> do
            logDebug $ ExportSignatureMsg contractPath
            liftProcess $
                readProcessWithExitCode contractPath ["export-signature"] ""

liftProcess ::
       (LastMember m effs, MonadIO m, FromJSON b, Member (LogMsg ContractExeLogMsg) effs, Member (Error PABError) effs)
    => IO (ExitCode, String, String)
    -> Eff effs b
liftProcess process = do
    (exitCode, stdout, stderr) <- sendM $ liftIO process
    case exitCode of
        ExitFailure code -> do
            logDebug $ ProcessExitFailure stderr
            throwError $ ContractCommandError code (Text.pack stderr)
        ExitSuccess -> do
            logDebug $ ContractResponse stdout
            case JSON.eitherDecode (BSL8.pack stdout) of
                Right value -> pure value
                Left err    -> throwError $ ContractCommandError 0 (Text.pack err)

-- data ExternalProcessContract

-- instance PABContract ExternalProcessContract where

    -- type ContractInput ExternalProcessContract = State.ContractRequest JSON.Value
    -- type ContractState

-- type Request t = State.ContractRequest (Input t)

-- -- | The state of a contract instance.
-- type State t = State.ContractResponse (ObsState t) (Err t) (IntState t) (OpenRequest t)
data ContractExeLogMsg =
    InvokeContractMsg
    | InitContractMsg FilePath
    | UpdateContractMsg FilePath (ContractRequest Value)
    | ExportSignatureMsg FilePath
    | ProcessExitFailure String
    | ContractResponse String
    | Migrating
    | InvokingEndpoint String Value
    | EndpointInvocationResponse [Text]
    | ContractExePABError PABError
    | StartingPABBackendServer Int
    | StartingMetadataServer Int
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty ContractExeLogMsg where
    pretty = \case
        InvokeContractMsg -> "InvokeContract"
        InitContractMsg fp -> fromString fp <+> "init"
        UpdateContractMsg fp vl ->
            let pl = BSL8.unpack (JSON.encodePretty vl) in
            fromString fp
            <+> "update"
            <+> fromString pl
        ExportSignatureMsg fp -> fromString fp <+> "export-signature"
        ProcessExitFailure err -> "ExitFailure" <+> pretty err
        ContractResponse str -> pretty str
        Migrating -> "Migrating"
        InvokingEndpoint s v ->
            "Invoking:" <+> pretty s <+> "/" <+> viaShow v
        EndpointInvocationResponse v ->
            hang 2 $ vsep ("Invocation response:" : fmap pretty v)
        ContractExePABError e ->
            "PAB error:" <+> pretty e
        StartingPABBackendServer port ->
            "Starting PAB backend server on port:" <+> pretty port
        StartingMetadataServer port ->
            "Starting metadata server on port:" <+> pretty port

instance ToObject ContractExeLogMsg where
    toObject v = \case
        InvokeContractMsg -> mkObjectStr "invoking contract" ()
        InitContractMsg fp ->
            mkObjectStr "Initialising contract" (Tagged @"file_path" fp)
        UpdateContractMsg fp rq ->
            let f =  Tagged @"file_path" fp in
            mkObjectStr "updating contract" $ case v of
                MaximalVerbosity -> Left (f, rq)
                _                -> Right f
        ExportSignatureMsg fp ->
            mkObjectStr "exporting signature" (Tagged @"file_path" fp)
        ProcessExitFailure f ->
            mkObjectStr "process exit failure" (Tagged @"error" f)
        ContractResponse r ->
            mkObjectStr "received contract response" $
                case v of
                    MaximalVerbosity -> Left (Tagged @"response" r)
                    _                -> Right ()
        Migrating -> mkObjectStr "migrating database" ()
        InvokingEndpoint ep vl ->
            mkObjectStr "Invoking endpoint" $
                case v of
                    MinimalVerbosity -> Left (Tagged @"endpoint" ep)
                    _                -> Right (Tagged @"endpoint" ep, Tagged @"argument" vl)
        EndpointInvocationResponse lns ->
            mkObjectStr "endpoint invocation response"  (Tagged @"reponse" lns)
        ContractExePABError err ->
            mkObjectStr "contract executable error" (Tagged @"error" err)
        StartingPABBackendServer i ->
            mkObjectStr "starting PAB backend server" (Tagged @"port" i)
        StartingMetadataServer i ->
            mkObjectStr "starting PAB metadata server" (Tagged @"port" i)
