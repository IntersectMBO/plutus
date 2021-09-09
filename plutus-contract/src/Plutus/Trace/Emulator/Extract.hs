{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-
Extract validators and partial transactions from emulator traces
-}
module Plutus.Trace.Emulator.Extract(
  writeScriptsTo,
  showStats,
  ScriptsConfig(..),
  Command(..)
) where

import qualified Cardano.Api                 as C
import qualified Cardano.Api.Shelley         as C
import qualified Control.Foldl               as L
import           Control.Monad.Freer         (run)
import qualified Data.Aeson                  as Aeson
import           Data.Aeson.Encode.Pretty    (encodePretty)
import qualified Data.ByteString.Lazy        as BSL
import           Data.Foldable               (traverse_)
import           Data.Int                    (Int64)
import           Data.Monoid                 (Sum (..))
import           Data.Text.Prettyprint.Doc   (Pretty (..))
import           Flat                        (flat)
import           Ledger.Constraints.OffChain (UnbalancedTx (..))
import           Ledger.Index                (ScriptValidationEvent (..), ValidatorMode (..), getScript)
import           Plutus.Contract.Wallet      (export)
import           Plutus.Trace.Emulator       (EmulatorConfig, EmulatorTrace)
import qualified Plutus.Trace.Emulator       as Trace
import           Plutus.V1.Ledger.Api        (ExBudget (..))
import           Plutus.V1.Ledger.Scripts    (Script (..))
import qualified Streaming.Prelude           as S
import           System.Directory            (createDirectoryIfMissing)
import           System.FilePath             ((</>))
import           Text.Printf                 (printf)
import qualified Wallet.Emulator.Folds       as Folds
import           Wallet.Emulator.Stream      (foldEmulatorStreamM)

-- | Configuration for 'writeScriptsTo'
data ScriptsConfig =
    ScriptsConfig
        { scPath    :: FilePath -- ^ Folder the extracted scripts should be written to
        , scCommand :: Command -- ^ Whether to write out complete transactions or just the validator scripts
        }

-- | Command for 'writeScriptsTo'
data Command =
    Scripts -- ^ Write out validator scripts only (flat encoding)
        { unappliedValidators :: ValidatorMode -- ^ Whether to write fully applied or unapplied validators
        }
    | Transactions  -- ^ Write out partial transactions
        { networkId          :: C.NetworkId -- ^ Network ID to use when creating addresses
        , protocolParamsJSON :: FilePath -- ^ Location of a JSON file with protocol parameters
        }
    deriving stock (Show, Eq)

{-| Run an emulator trace and write the applied scripts to a file in Flat format
    using the name as a prefix.
-}
writeScriptsTo
    :: ScriptsConfig -- ^ Configuration
    -> String -- ^ Prefix to be used for file names
    -> EmulatorTrace a -- ^ Emulator trace to extract transactions from
    -> EmulatorConfig -- ^ Emulator config
    -> IO (Sum Int64, ExBudget) -- Total size and 'ExBudget' of extracted scripts
writeScriptsTo ScriptsConfig{scPath, scCommand} prefix trace emulatorCfg = do
    let stream = Trace.runEmulatorStream emulatorCfg trace
        getEvents :: Folds.EmulatorEventFold a -> a
        getEvents theFold = S.fst' $ run $ foldEmulatorStreamM (L.generalize theFold) stream
    createDirectoryIfMissing True scPath
    case scCommand of
        Scripts mode -> do
            foldMap (uncurry $ writeScript scPath prefix mode) (zip [1::Int ..] $ getEvents Folds.scriptEvents)
        Transactions{networkId, protocolParamsJSON} -> do
            bs <- BSL.readFile protocolParamsJSON
            case Aeson.eitherDecode bs of
                Left err -> putStrLn err
                Right params ->
                    traverse_
                        (uncurry $ writeTransaction params networkId scPath prefix)
                        (zip [1::Int ..] $ getEvents Folds.walletTxBalanceEvents)
            pure mempty

{- There's an instance of Codec.Serialise for
    Script in Scripts.hs (see Note [Using Flat inside CBOR instance of Script]),
    which wraps Flat-encoded bytestings in CBOR, but that's not used here: we
    just use unwrapped Flat because that's more convenient for use with the
    `plc` command, for example.
-}
writeScript :: FilePath -> String -> ValidatorMode -> Int -> ScriptValidationEvent -> IO (Sum Int64, ExBudget)
writeScript fp prefix mode idx event@ScriptValidationEvent{sveResult} = do
    let filename = fp </> prefix <> "-" <> show idx <> filenameSuffix mode <> ".flat"
        bytes = BSL.fromStrict . flat . unScript . getScript mode $ event
        byteSize = BSL.length bytes
    putStrLn $ "Writing script: " <> filename <> " (" <> either show (showStats byteSize . fst) sveResult <> ")"
    BSL.writeFile filename bytes
    pure (Sum byteSize, foldMap fst sveResult)

showStats :: Int64 -> ExBudget -> String
showStats byteSize (ExBudget exCPU exMemory) = "Size: " <> size <> "kB, Cost: " <> show exCPU <> ", " <> show exMemory
    where
        size = printf ("%.1f"::String) (fromIntegral byteSize / 1024.0 :: Double)

writeTransaction :: C.ProtocolParameters -> C.NetworkId -> FilePath -> String -> Int -> UnbalancedTx -> IO ()
writeTransaction params networkId fp prefix idx tx = do
    let filename1 = fp </> prefix <> "-" <> show idx <> ".json"
    case export params networkId tx of
        Left err ->
            putStrLn $ "Export tx failed for " <> filename1 <> ". Reason: " <> show (pretty err)
        Right exportTx -> do
            putStrLn $ "Writing partial transaction JSON: " <> filename1
            BSL.writeFile filename1 $ encodePretty exportTx

filenameSuffix :: ValidatorMode -> String
filenameSuffix FullyAppliedValidators = ""
filenameSuffix UnappliedValidators    = "-unapplied"
