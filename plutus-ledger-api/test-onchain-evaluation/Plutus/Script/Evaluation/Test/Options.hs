{-# LANGUAGE ApplicativeDo   #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData      #-}

module Plutus.Script.Evaluation.Test.Options (
    Options (..),
    parseOptions,
    parserInfo,
) where

import GHC.Conc (numCapabilities)
import Options.Applicative qualified as O

data Options = Options
    { optsDir          :: String
    , optsEventFileExt :: String
    , optsConcurrency  :: Int
    }

parseOptions :: O.Parser Options
parseOptions = do
    optsDir <-
        O.option O.str $
            mconcat
                [ O.short 'd'
                    , O.long "dir"
                , O.metavar "DIR"
                , O.help "dir containing event dump files"
                ]
    optsEventFileExt <-
        O.option O.str $
            mconcat
                [ O.long "event-file-extension"
                , O.value "event"
                , O.metavar "EVENT_FILE_EXTENSION"
                ]
    optsConcurrency <-
        O.option O.auto $
            mconcat
                [ O.long "concurrency"
                , O.value numCapabilities
                , O.metavar "CONCURRENCY"
                , O.help "How many threads to use"
                ]
    pure Options{..}

parserInfo :: O.ParserInfo Options
parserInfo =
    O.info
        (parseOptions O.<**> O.helper)
        (O.fullDesc <> O.header "Run script evaluation regression test")
