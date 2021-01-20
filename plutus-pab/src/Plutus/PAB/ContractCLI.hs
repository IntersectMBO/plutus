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
module Plutus.PAB.ContractCLI
    ( commandLineApp
    , commandLineApp'
    , runCliCommand
    , runUpdate
    , Command(..)
    ) where

import           Control.Monad.IO.Class          (MonadIO, liftIO)
import           Data.Aeson                      (FromJSON, ToJSON)
import qualified Data.Aeson                      as JSON
import qualified Data.Aeson.Encode.Pretty        as JSON
import           Data.Bifunctor                  (bimap)
import qualified Data.ByteString                 as BS
import qualified Data.ByteString.Char8           as BS8
import qualified Data.ByteString.Lazy            as BSL
import           Data.Proxy                      (Proxy (..))
import           Data.Row                        (AllUniqueLabels, Forall, type (.\\))
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
import qualified System.IO

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

runCliCommand :: forall s s2 m.
       ( AllUniqueLabels (Input s)
       , Forall (Input s) FromJSON
       , Forall (Output s) ToJSON
       , Forall (Input s) ToJSON
       , EndpointToSchema (s .\\ s2)
       , MonadIO m
       )
    => Proxy s2
    -> Contract s Text ()
    -> Command
    -> m (Either BS8.ByteString BS8.ByteString)
runCliCommand _ schema Initialise = pure $ Right $ BSL.toStrict $ JSON.encodePretty $ ContractState.initialiseContract schema
runCliCommand _ schema Update = do
    arg <- liftIO BS.getContents
    pure $ runUpdate schema arg
runCliCommand _ _ ExportSignature = do
  let r = endpointsToSchemas @(s .\\ s2)
  pure $ Right $ BSL.toStrict $ JSON.encodePretty r

runUpdate :: forall s.
    ( AllUniqueLabels (Input s)
    , Forall (Input s) FromJSON
    , Forall (Output s) ToJSON
    , Forall (Input s) ToJSON
    )
    => Contract s Text ()
    -> BS.ByteString
    -> Either BS8.ByteString BS8.ByteString
runUpdate contract arg =
    bimap
        (BSL.toStrict . JSON.encodePretty . Text.pack)
        (BSL.toStrict . JSON.encodePretty . ContractState.insertAndUpdateContract contract)
        (JSON.eitherDecode $ BSL.fromStrict arg)

-- | Make a command line app with a schema that includes all of the contract's
--   endpoints except the 'BlockchainActions' ones.
commandLineApp :: forall s.
       ( AllUniqueLabels (Input s)
       , Forall (Input s) FromJSON
       , Forall (Input s) ToJSON
       , Forall (Output s) ToJSON
       , EndpointToSchema (s .\\ BlockchainActions)
       )
    => Contract s Text ()
    -> IO ()
commandLineApp = commandLineApp' @s @BlockchainActions (Proxy @BlockchainActions)

-- | Make a command line app for a contract, excluding some of the contract's
--   endpoints from the generated schema.
commandLineApp' :: forall s s2.
       ( AllUniqueLabels (Input s)
       , Forall (Input s) FromJSON
       , Forall (Input s) ToJSON
       , Forall (Output s) ToJSON
       , EndpointToSchema (s .\\ s2)
       )
    => Proxy s2
    -> Contract s Text ()
    -> IO ()
commandLineApp' p schema = do
    cmd <-
        customExecParser
            (prefs $ disambiguate <> showHelpOnEmpty <> showHelpOnError)
            (info (helper <*> versionOption <*> commandLineParser) idm)
    result <- runCliCommand p schema cmd
    case result of
        Left err -> do
            BS8.hPut System.IO.stderr "Error "
            BS8.hPut System.IO.stderr (BSL.toStrict $ JSON.encodePretty err)
            exitWith $ ExitFailure 1
        Right response -> do
            BS8.putStrLn response
            exitSuccess
