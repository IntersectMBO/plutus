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

'ContractEffect' handler for contracts compiled that use the CLI
interface (see 'Plutus.PAB.ContractCLI').

-}
module Plutus.PAB.Effects.Contract.ContractExe(
    ContractExe(..)
    , handleContractEffectContractExe
    , ContractExeLogMsg(..)
    ) where

import           Cardano.BM.Data.Tracer.Extras                    (StructuredLog (..))
import           Control.Monad.Freer                              (Eff, LastMember, Member, send, sendM, type (~>))
import           Control.Monad.Freer.Error                        (Error, throwError)
import           Control.Monad.Freer.Extras.Log                   (LogMsg (..), logDebug, logError, logWarn)
import           Control.Monad.IO.Class                           (MonadIO (..))
import           Data.Aeson                                       (FromJSON (..), ToJSON (..), Value)
import qualified Data.Aeson                                       as JSON
import qualified Data.Aeson.Encode.Pretty                         as JSON
import qualified Data.ByteString.Lazy.Char8                       as BSL8
import           Data.Foldable                                    (traverse_)
import qualified Data.HashMap.Strict                              as HM
import qualified Data.Text                                        as Text
import           Data.Text.Prettyprint.Doc                        (Pretty, pretty, (<+>))
import           GHC.Generics                                     (Generic)
import           Plutus.Contract.Effects                          (PABReq, PABResp)
import           Plutus.Contract.Resumable                        (Response)
import           Plutus.Contract.State                            (ContractRequest (..), ContractResponse)
import qualified Plutus.Contract.State                            as ContractState
import           Plutus.PAB.Core.ContractInstance.RequestHandlers (ContractInstanceMsg (ContractLog))
import           Plutus.PAB.Effects.Contract                      (ContractEffect (..), PABContract (..))
import           Plutus.PAB.Events.Contract                       (ContractInstanceId (..))
import           Plutus.PAB.Monitoring.PABLogMsg                  (ContractExeLogMsg (..), PABMultiAgentMsg (..))
import           Plutus.PAB.Types                                 (PABError (ContractCommandError))
import           System.Exit                                      (ExitCode (ExitFailure, ExitSuccess))
import           System.Process                                   (readProcessWithExitCode)

instance PABContract ContractExe where
    type ContractDef ContractExe = ContractExe
    type State ContractExe = ContractResponse Value Value Value PABReq

    serialisableState _ = id

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
    forall m effs.
       ( Member (LogMsg ContractExeLogMsg) effs
       , Member (LogMsg (PABMultiAgentMsg ContractExe)) effs
       , Member (Error PABError) effs
       , LastMember m effs
       , MonadIO m)
    => ContractEffect ContractExe
    ~> Eff effs
handleContractEffectContractExe =
    \case
        InitialState i (ContractExe contractPath) -> do
            logDebug $ InitContractMsg contractPath
            result <- liftProcess $ readProcessWithExitCode contractPath ["init"] ""
            logNewMessages i result
            pure result
        UpdateContract i (ContractExe contractPath) (oldState :: ContractResponse Value Value Value PABReq) (input :: Response PABResp) -> do
            let req :: ContractRequest Value Value
                req = ContractRequest{oldState = ContractState.newState oldState, event = toJSON <$> input}
                encodedRequest = JSON.encodePretty req
                pl = BSL8.unpack encodedRequest
            result <- liftProcess $ readProcessWithExitCode contractPath ["update"] pl
            logNewMessages i result
            pure result
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
            logError $ ProcessExitFailure stderr
            throwError $ ContractCommandError code (Text.pack stderr)
        ExitSuccess -> do
            case JSON.eitherDecode (BSL8.pack stdout) of
                Right value -> pure value
                Left err    -> do
                    logWarn $ AContractResponse stdout
                    logError $ ContractResponseJSONDecodingError err
                    throwError $ ContractCommandError 0 (Text.pack err)

logNewMessages ::
    forall effs.
    Member (LogMsg (PABMultiAgentMsg ContractExe)) effs
    => ContractInstanceId
    -> ContractResponse Value Value Value PABReq
    -> Eff effs ()
logNewMessages i ContractState.ContractResponse{ContractState.lastLogs} =
    traverse_ (send @(LogMsg (PABMultiAgentMsg ContractExe)) . LMessage . fmap (ContractInstanceLog . ContractLog i)) lastLogs
