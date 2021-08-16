{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}

module Main(main, ExportTx(..)) where

import qualified Cardano.Api                    as C
import qualified Cardano.Api.Shelley            as C
import qualified Control.Foldl                  as L
import           Control.Monad.Freer            (run)
import           Data.Aeson                     (FromJSON (..), ToJSON (..), Value (Object), object, (.:), (.=))
import qualified Data.Aeson                     as Aeson
import           Data.Aeson.Encode.Pretty       (encodePretty)
import           Data.Bitraversable             (bitraverse)
import           Data.ByteArray.Encoding        (Base (Base16), convertToBase)
import qualified Data.ByteString.Lazy           as BSL
import           Data.Default                   (Default (..))
import           Data.Foldable                  (traverse_)
import           Data.Int                       (Int64)
import           Data.Map                       (Map)
import qualified Data.Map                       as Map
import           Data.Maybe                     (mapMaybe)
import           Data.Monoid                    (Sum (..))
import           Data.Proxy                     (Proxy (..))
import           Data.Text                      (Text)
import qualified Data.Text.Encoding             as Text
import           Data.Text.Prettyprint.Doc      (Pretty (..))
import           Data.Typeable                  (Typeable)
import           Flat                           (flat)
import           GHC.Generics                   (Generic)
import qualified Ledger                         as Plutus
import           Ledger.Bytes                   (LedgerBytes (..))
import           Ledger.Constraints.OffChain    (UnbalancedTx (..))
import           Ledger.Crypto                  (PubKey (..))
import           Ledger.Index                   (ScriptType (..), ScriptValidationEvent (..))
import           Options.Applicative
import qualified Plutus.Contract.CardanoAPI     as CardanoAPI
import qualified Plutus.Contracts.Crowdfunding  as Crowdfunding
import qualified Plutus.Contracts.Uniswap.Trace as Uniswap
import           Plutus.Trace.Emulator          (EmulatorConfig, EmulatorTrace)
import qualified Plutus.Trace.Emulator          as Trace
import           Plutus.V1.Ledger.Api           (ExBudget (..))
import           Plutus.V1.Ledger.Scripts       (Script (..))
import qualified Spec.Auction                   as Auction
import qualified Spec.Currency                  as Currency
import qualified Spec.Escrow                    as Escrow
import qualified Spec.Future                    as Future
import qualified Spec.GameStateMachine          as GameStateMachine
import qualified Spec.MultiSig                  as MultiSig
import qualified Spec.MultiSigStateMachine      as MultiSigStateMachine
import qualified Spec.PingPong                  as PingPong
import qualified Spec.Prism                     as Prism
import qualified Spec.PubKey                    as PubKey
import qualified Spec.Stablecoin                as Stablecoin
import qualified Spec.TokenAccount              as TokenAccount
import qualified Spec.Vesting                   as Vesting
import qualified Streaming.Prelude              as S
import           System.Directory               (createDirectoryIfMissing)
import           System.FilePath                ((</>))
import           Text.Printf                    (printf)
import qualified Wallet.Emulator.Folds          as Folds
import           Wallet.Emulator.Stream         (foldEmulatorStreamM)

data Command =
    Scripts{ unappliedValidators :: ValidatorMode }
    | Transactions{ networkId :: C.NetworkId, protocolParamsJSON :: FilePath }
    deriving stock (Show, Eq)

writeWhat :: Command -> String
writeWhat (Scripts FullyAppliedValidators) = "scripts (fully applied)"
writeWhat (Scripts UnappliedValidators)    = "scripts (unapplied)"
writeWhat Transactions{}                   = "transactions"

pathParser :: Parser FilePath
pathParser = strArgument (metavar "SCRIPT_PATH" <> help "output path")

protocolParamsParser :: Parser FilePath
protocolParamsParser = strOption (long "protocol-parameters" <> short 'p' <> help "Path to protocol parameters JSON file" <> showDefault <> value "protocol-parameters.json")

networkIdParser :: Parser C.NetworkId
networkIdParser =
    let p = C.Testnet . C.NetworkMagic <$> option auto (long "network-magic" <> short 'n' <> help "Cardano network magic. If none is specified, mainnet addresses are generated.")
    in p <|> pure C.Mainnet

commandParser :: Parser Command
commandParser = hsubparser $ mconcat [scriptsParser, transactionsParser]

scriptsParser :: Mod CommandFields Command
scriptsParser =
    command "scripts" $
    info
        (Scripts <$> flag FullyAppliedValidators UnappliedValidators (long "unapplied-validators" <> short 'u' <> help "Write the unapplied validator scripts" <> showDefault))
        (fullDesc <> progDesc "Write fully applied validator scripts")

transactionsParser :: Mod CommandFields Command
transactionsParser =
    command "transactions" $
    info
        (Transactions <$> networkIdParser <*> protocolParamsParser)
        (fullDesc <> progDesc "Write partial transactions")

data ScriptsConfig =
    ScriptsConfig
        { scPath    :: FilePath
        , scCommand :: Command
        }

progParser :: ParserInfo ScriptsConfig
progParser =
    let p = ScriptsConfig <$> pathParser <*> commandParser
    in info
        (p <**> helper)
        (fullDesc
        <> progDesc "Run a number of emulator traces and write all validator scripts and/or partial transactions to SCRIPT_PATH"
        <> header "plutus-use-cases-scripts - extract applied validators and partial transactions from emulator traces"
        )

main :: IO ()
main = execParser progParser >>= writeScripts

writeScripts :: ScriptsConfig -> IO ()
writeScripts config = do
    putStrLn $ "Writing " <> writeWhat (scCommand config) <> " to: " <> scPath config
    (Sum size, exBudget) <- foldMap (uncurry3 (writeScriptsTo config))
        [ ("auction_1", Auction.auctionTrace1, Auction.auctionEmulatorCfg)
        , ("auction_2", Auction.auctionTrace2, Auction.auctionEmulatorCfg)
        , ("crowdfunding-success", Crowdfunding.successfulCampaign, def)
        , ("currency", Currency.currencyTrace, def)
        , ("escrow-redeem_1", Escrow.redeemTrace, def)
        , ("escrow-redeem_2", Escrow.redeem2Trace, def)
        , ("escrow-refund", Escrow.refundTrace, def)
        , ("future-increase-margin", Future.increaseMarginTrace, def)
        , ("future-settle-early", Future.settleEarlyTrace, def)
        , ("future-pay-out", Future.payOutTrace, def)
        , ("game-sm-success", GameStateMachine.successTrace, def)
        , ("game-sm-success_2", GameStateMachine.successTrace2, def)
        , ("multisig-success", MultiSig.succeedingTrace, def)
        , ("multisig-failure", MultiSig.failingTrace, def)
        , ("multisig-sm", MultiSigStateMachine.lockProposeSignPay 3 2, def)
        , ("ping-pong", PingPong.pingPongTrace, def)
        , ("ping-pong_2", PingPong.twoPartiesTrace, def)
        , ("prism", Prism.prismTrace, def)
        , ("pubkey", PubKey.pubKeyTrace, def)
        , ("stablecoin_1", Stablecoin.stablecoinTrace, def)
        , ("stablecoin_2", Stablecoin.maxReservesExceededTrace, def)
        , ("token-account", TokenAccount.tokenAccountTrace, def)
        , ("vesting", Vesting.retrieveFundsTrace, def)
        , ("uniswap", Uniswap.uniswapTrace, def)
        ]
    if size > 0 then
        putStrLn $ "Total " <> showStats size exBudget
    else pure ()

{-| Run an emulator trace and write the applied scripts to a file in Flat format
    using the name as a prefix.
-}
writeScriptsTo
    :: ScriptsConfig
    -> String
    -> EmulatorTrace a
    -> EmulatorConfig
    -> IO (Sum Int64, ExBudget)
writeScriptsTo ScriptsConfig{scPath, scCommand} prefix trace emulatorCfg = do
    let (scriptEvents, balanceEvents) =
            S.fst'
            $ run
            $ foldEmulatorStreamM (L.generalize theFold)
            $ Trace.runEmulatorStream emulatorCfg trace

    createDirectoryIfMissing True scPath
    case scCommand of
        Scripts mode -> do
            foldMap (uncurry $ writeScript scPath prefix mode) (zip [1::Int ..] scriptEvents)
        Transactions{networkId, protocolParamsJSON} -> do
            bs <- BSL.readFile protocolParamsJSON
            case Aeson.eitherDecode bs of
                Left err -> putStrLn err
                Right params -> traverse_ (uncurry $ writeTransaction params networkId scPath prefix) (zip [1::Int ..] balanceEvents)
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

-- | `uncurry3` converts a curried function to a function on triples.
uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

theFold :: Folds.EmulatorEventFold ([ScriptValidationEvent], [UnbalancedTx])
theFold = (,) <$> Folds.scriptEvents <*> Folds.walletTxBalanceEvents

{- Note [Keys in ExportTx]

The wallet backend (receiver of 'ExportTx' values) expectes the public keys in the
'signatories' field to be 'Cardano.Crypto.Wallet.XPub' keys - extended public keys
of 64 bytes. In the emulator we only deal with ED25519 keys of 32 bytes. Until that
is changed (https://jira.iohk.io/browse/SCP-2644) we simply append each of our keys
to itself in order to get a key of the correct length.

-}

-- | Partial transaction that can be balanced by the wallet backend.
data ExportTx =
        ExportTx
            { partialTx   :: C.Tx C.AlonzoEra -- ^ The transaction itself
            , lookups     :: [ExportTxInput] -- ^ The tx outputs for all inputs spent by the partial tx
            , signatories :: [Text] -- ^ Key(s) that we expect to be used for balancing & signing. (Advisory) See note [Keys in ExportT]
            }
    deriving stock (Generic, Typeable)

data ExportTxInput = ExportTxInput{txIn :: C.TxIn, txOut :: C.TxOut C.AlonzoEra}
    deriving stock (Generic, Typeable)
    deriving anyclass (ToJSON)

instance ToJSON ExportTx where
    toJSON ExportTx{partialTx, lookups, signatories} =
        object
            [ "transaction" .= toJSON (C.serialiseToTextEnvelope Nothing partialTx)
            , "inputs"      .= toJSON lookups
            , "signatories" .= toJSON signatories
            ]

instance FromJSON ExportTx where
    parseJSON (Object v) =
        ExportTx
            <$> ((v .: "transaction") >>= either (fail . show) pure . C.deserialiseFromTextEnvelope (C.proxyToAsType Proxy))
            <*> pure mempty -- FIXME: How to deserialise Utxo / [(TxIn, TxOut)] ) see https://github.com/input-output-hk/cardano-node/issues/3051
            <*> v .: "signatories"
    parseJSON _ = fail "Expexted Object"

export :: C.ProtocolParameters -> C.NetworkId -> UnbalancedTx -> Either CardanoAPI.ToCardanoError ExportTx
export params networkId UnbalancedTx{unBalancedTxTx, unBalancedTxUtxoIndex, unBalancedTxRequiredSignatories} =
    ExportTx
        <$> mkTx params networkId unBalancedTxTx
        <*> mkLookups networkId unBalancedTxUtxoIndex
        <*> mkSignatories unBalancedTxRequiredSignatories

mkTx :: C.ProtocolParameters -> C.NetworkId -> Plutus.Tx -> Either CardanoAPI.ToCardanoError (C.Tx C.AlonzoEra)
mkTx params networkId = fmap (C.makeSignedTransaction []) . CardanoAPI.toCardanoTxBody (Just params) networkId

mkLookups :: C.NetworkId -> Map Plutus.TxOutRef Plutus.TxOut -> Either CardanoAPI.ToCardanoError [ExportTxInput]
mkLookups networkId = fmap (fmap $ uncurry ExportTxInput) . traverse (bitraverse CardanoAPI.toCardanoTxIn (CardanoAPI.toCardanoTxOut networkId)) . Map.toList

mkSignatories :: Map Plutus.PubKeyHash (Maybe Plutus.PubKey) -> Either CardanoAPI.ToCardanoError [Text]
mkSignatories =
    -- see note [Keys in ExportTx]
    Right . fmap (\(PubKey (LedgerBytes k)) -> Text.decodeUtf8 $ convertToBase Base16 (k <> k)) . mapMaybe snd . Map.toList

data ValidatorMode = FullyAppliedValidators | UnappliedValidators
    deriving (Eq, Ord, Show)

getScript :: ValidatorMode -> ScriptValidationEvent -> Script
getScript FullyAppliedValidators ScriptValidationEvent{sveScript} = sveScript
getScript UnappliedValidators ScriptValidationEvent{sveType} =
    case sveType of
        ValidatorScript (Plutus.Validator script) _    -> script
        MintingPolicyScript (Plutus.MintingPolicy mps) -> mps

filenameSuffix :: ValidatorMode -> String
filenameSuffix FullyAppliedValidators = ""
filenameSuffix UnappliedValidators    = "-unapplied"
