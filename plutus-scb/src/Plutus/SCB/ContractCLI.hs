{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-|
Create a command line application from a @Contract schema Text ()@. For example:

> game :: AsContractError e => Contract GameSchema e ()
> game = lock <|> guess
>
> ...
>
> main :: IO ()
> main = commandLineApp game

-}
module Plutus.SCB.ContractCLI
    ( commandLineApp
    , runCliCommand
    , Command(..)
    ) where

import           Control.Monad.IO.Class          (MonadIO, liftIO)
import           Data.Aeson                      (FromJSON, ToJSON)
import qualified Data.Aeson                      as JSON
import qualified Data.Aeson.Encode.Pretty        as JSON
import           Data.Bifunctor                  (bimap)
import qualified Data.ByteString.Lazy            as BSL
import qualified Data.ByteString.Lazy.Char8      as BS8
import           Data.Row                        (type (.\\), AllUniqueLabels, Forall)
import           Data.Text                       (Text)
import qualified Data.Text                       as Text
import           Git                             (gitRev)
import           Language.Plutus.Contract        (BlockchainActions, Contract)
import           Language.Plutus.Contract.Schema (Input, Output)
import qualified Language.Plutus.Contract.State  as ContractState
import           Options.Applicative             (CommandFields, Mod, Parser, command, customExecParser, disambiguate,
                                                  fullDesc, help, helper, idm, info, infoOption, long, prefs, progDesc,
                                                  short, showHelpOnEmpty, showHelpOnError, subparser)
import           Playground.Schema               (EndpointToSchema, endpointsToSchemas)
import           System.Exit                     (ExitCode (ExitFailure), exitSuccess, exitWith)
data Command
    = Initialise
    | Update
    | ExportSignature
    deriving (Show, Eq)

versionOption :: Parser (a -> a)
versionOption =
    infoOption
        (Text.unpack gitRev)
        (short 'v' <> long "version" <> help "Show the version")

commandLineParser :: Parser Command
commandLineParser = subparser $ mconcat [initialiseParser, updateParser, exportSignatureParser]

initialiseParser :: Mod CommandFields Command
initialiseParser =
    command "init" $
    info (pure Initialise) (fullDesc <> progDesc "Initialise the contract.")

updateParser :: Mod CommandFields Command
updateParser =
    command "update" $
    info
        (pure Update)
        (fullDesc <>
         progDesc "Update the contract. The request must be supplied on stdin.")


exportSignatureParser :: Mod CommandFields Command
exportSignatureParser =
    command "export-signature" $
    info (pure ExportSignature) (fullDesc <> progDesc "Export the contract's signature.")

runCliCommand :: forall s m.
       ( AllUniqueLabels (Input s)
       , Forall (Input s) FromJSON
       , Forall (Output s) ToJSON
       , Forall (Input s) ToJSON
       , EndpointToSchema (s .\\ BlockchainActions)
       , MonadIO m
       )
    => Contract s Text ()
    -> Command
    -> m (Either BS8.ByteString BS8.ByteString)
runCliCommand schema Initialise = pure $ bimap JSON.encodePretty JSON.encodePretty $ ContractState.initialiseContract schema
runCliCommand schema Update = do
    arg <- liftIO BSL.getContents
    pure $ bimap JSON.encodePretty JSON.encodePretty $
        case JSON.eitherDecode arg of
            Left err      -> Left $ Text.pack err
            Right request -> ContractState.insertAndUpdateContract schema request
runCliCommand _ ExportSignature = do
  let r = endpointsToSchemas @(s .\\ BlockchainActions)
  pure $ Right $ JSON.encodePretty r

commandLineApp ::
       ( AllUniqueLabels (Input s)
       , Forall (Input s) FromJSON
       , Forall (Input s) ToJSON
       , Forall (Output s) ToJSON
       , EndpointToSchema (s .\\ BlockchainActions)
       )
    => Contract s Text ()
    -> IO ()
commandLineApp schema = do
    cmd <-
        customExecParser
            (prefs $ disambiguate <> showHelpOnEmpty <> showHelpOnError)
            (info (helper <*> versionOption <*> commandLineParser) idm)
    result <- runCliCommand schema cmd
    case result of
        Left err -> do
            BS8.putStrLn $ JSON.encodePretty err
            exitWith $ ExitFailure 1
        Right response -> do
            BS8.putStrLn response
            exitSuccess
