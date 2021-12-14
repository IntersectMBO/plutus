{-# LANGUAGE OverloadedStrings #-}
module Foundation.Check.Config
    ( Config(..)
    , Seed
    , DisplayOption(..)
    , defaultConfig
    , parseArgs
    , configHelp
    ) where

import           Basement.Imports
import           Basement.IntegralConv
import           Foundation.String.Read
import           Foundation.Check.Gen

type Seed = Word64

data DisplayOption =
      DisplayTerminalErrorOnly
    | DisplayGroupOnly
    | DisplayTerminalVerbose
    deriving (Eq, Ord, Enum, Bounded, Show)

data Config = Config
    { udfSeed      :: Maybe Seed -- ^ optional user specified seed
    , getGenParams :: !GenParams
        -- ^ Parameters for the generator
        --
        -- default:
        --   * 32bits long numbers;
        --   * array of 512 elements max;
        --   * string of 8192 bytes max.
        --
    , numTests     :: !Word64
        -- ^ the number of tests to perform on every property.
        --
        -- default: 100
    , listTests      :: Bool
    , testNameMatch  :: [String]
    , displayOptions :: !DisplayOption
    , helpRequested  :: Bool
    }

-- | create the default configuration
--
-- see @Config@ for details
defaultConfig :: Config
defaultConfig = Config
    { udfSeed      = Nothing
    , getGenParams = params
    , numTests     = 100
    , listTests    = False
    , testNameMatch  = []
    , displayOptions = DisplayGroupOnly
    , helpRequested  = False
    }
  where
    params = GenParams
        { genMaxSizeIntegral = 32   -- 256 bits maximum numbers
        , genMaxSizeArray    = 512  -- 512 elements
        , genMaxSizeString   = 8192 -- 8K string
        }

type ParamError = String

getInteger :: String -> String -> Either ParamError Integer
getInteger optionName s =
    maybe (Left errMsg) Right $ readIntegral s
  where
    errMsg = "argument error for " <> optionName <> " expecting a number but got : " <> s

parseArgs :: [String] -> Config -> Either ParamError Config
parseArgs []                cfg   = Right cfg
parseArgs ["--seed"]       _      = Left "option `--seed' is missing a parameter"
parseArgs ("--seed":x:xs)  cfg    = getInteger "seed" x >>= \i -> parseArgs xs $ cfg { udfSeed = Just $ integralDownsize i }
parseArgs ["--tests"]      _      = Left "option `--tests' is missing a parameter"
parseArgs ("--tests":x:xs) cfg    = getInteger "tests" x >>= \i -> parseArgs xs $ cfg { numTests = integralDownsize i }
parseArgs ("--quiet":xs)   cfg    = parseArgs xs $ cfg { displayOptions = DisplayTerminalErrorOnly }
parseArgs ("--list-tests":xs) cfg = parseArgs xs $ cfg { listTests = True }
parseArgs ("--verbose":xs) cfg    = parseArgs xs $ cfg { displayOptions = DisplayTerminalVerbose }
parseArgs ("--help":xs)    cfg    = parseArgs xs $ cfg { helpRequested = True }
parseArgs (x:xs)           cfg    = parseArgs xs $ cfg { testNameMatch = x : testNameMatch cfg }

configHelp :: [String]
configHelp =
    [ "Usage: <program-name> [options] [test-name-match]\n"
    , "\n"
    , "Known options:\n"
    , "\n"
    , "  --seed <seed>: a 64bit positive number to use as seed to generate arbitrary value.\n"
    , "  --tests <tests>: the number of tests to perform for every property tests.\n"
    , "  --quiet: print only the errors to the standard output\n"
    , "  --verbose: print every property tests to the stand output.\n"
    , "  --list-tests: print all test names.\n"
    ]
