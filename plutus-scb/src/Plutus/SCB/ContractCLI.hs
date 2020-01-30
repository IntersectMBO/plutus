{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE UndecidableInstances       #-}

module Plutus.SCB.ContractCLI
    ( commandLineApp
    ) where

import           Control.Monad.IO.Class             (MonadIO, liftIO)
import           Data.Aeson                         (FromJSON, ToJSON)
import qualified Data.Aeson                         as JSON
import qualified Data.Aeson.Encode.Pretty           as JSON
import qualified Data.ByteString.Lazy               as BSL
import qualified Data.ByteString.Lazy.Char8         as BS8
import           Data.Row                           (AllUniqueLabels, Forall)
import           Data.Text                          (Text)
import qualified Data.Text                          as Text
import           Git                                (gitRev)
import           Language.Plutus.Contract.Request   (Contract (..))
import           Language.Plutus.Contract.Resumable (ResumableError (OtherError))
import           Language.Plutus.Contract.Schema    (Input, Output)
import           Language.Plutus.Contract.Servant   (Response, initialResponse, runUpdate)
import           Options.Applicative                (CommandFields, Mod, Parser, command, customExecParser,
                                                     disambiguate, fullDesc, help, helper, idm, info, infoOption, long,
                                                     prefs, progDesc, short, showHelpOnEmpty, showHelpOnError,
                                                     subparser)
import           System.Exit                        (ExitCode (ExitFailure, ExitSuccess), exitWith)

data Command
    = Initialise
    | Update
    deriving (Show, Eq)

versionOption :: Parser (a -> a)
versionOption =
    infoOption
        (Text.unpack gitRev)
        (short 'v' <> long "version" <> help "Show the version")

commandLineParser :: Parser Command
commandLineParser = commandParser

commandParser :: Parser Command
commandParser = subparser $ mconcat [initialiseParser, updateParser]

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

runCliCommand ::
       ( AllUniqueLabels (Input s)
       , AllUniqueLabels (Output s)
       , Forall (Input s) FromJSON
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       , MonadIO m
       )
    => Contract s Text ()
    -> Command
    -> m (Either (ResumableError Text) (Response s))
runCliCommand schema Initialise = pure $ initialResponse schema
runCliCommand schema Update = do
    arg <- liftIO BSL.getContents
    pure $
        case JSON.eitherDecode arg of
            Left err      -> Left $ OtherError $ Text.pack err
            Right request -> runUpdate schema request

commandLineApp ::
       ( AllUniqueLabels (Input s)
       , AllUniqueLabels (Output s)
       , Forall (Input s) FromJSON
       , Forall (Input s) ToJSON
       , Forall (Output s) ToJSON
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
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
            BS8.putStrLn $ JSON.encodePretty response
            exitWith ExitSuccess
