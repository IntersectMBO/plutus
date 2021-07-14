{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
module Main(main) where

import qualified Cardano.Api                    as C
import qualified Cardano.Binary                 as Binary
import qualified Control.Foldl                  as L
import           Control.Monad                  (when)
import           Control.Monad.Freer            (run)
import qualified Data.Aeson                     as Aeson
import           Data.Aeson.Encode.Pretty       (encodePretty)
import           Data.Bitraversable             (bitraverse)
import qualified Data.ByteString.Lazy           as BSL
import           Data.Default                   (Default (..))
import           Data.Foldable                  (traverse_)
import           Data.Map                       (Map)
import qualified Data.Map                       as Map
import           Data.Proxy                     (Proxy (..))
import           Data.Set                       (Set)
import qualified Data.Set                       as Set
import           Data.Text.Prettyprint.Doc      (Pretty (..))
import           Data.Typeable                  (Typeable)
import           Flat                           (flat)
import           GHC.Generics                   (Generic)
import qualified Ledger                         as Plutus
import           Ledger.Constraints.OffChain    (UnbalancedTx (..))
import           Ledger.Index                   (ScriptValidationEvent (sveScript))
import           Options.Applicative
import qualified Plutus.Contract.CardanoAPI     as CardanoAPI
import qualified Plutus.Contracts.Crowdfunding  as Crowdfunding
import qualified Plutus.Contracts.Uniswap.Trace as Uniswap
import           Plutus.Trace.Emulator          (EmulatorConfig, EmulatorTrace)
import qualified Plutus.Trace.Emulator          as Trace
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
import qualified Wallet.Emulator.Folds          as Folds
import           Wallet.Emulator.Stream         (foldEmulatorStreamM)

data Mode = Scripts | Transactions | Both
    deriving stock (Read, Show, Eq)

instance Ord Mode where
    x <= y = x == y || y == Both

writeWhat :: Mode -> String
writeWhat Scripts      = "scripts"
writeWhat Both         = "scripts and partial transactions"
writeWhat Transactions = "partial transactions"

pathParser :: Parser FilePath
pathParser = strArgument (metavar "SCRIPT_PATH" <> help "output path")

modeParser :: Parser Mode
modeParser = option auto (long "mode" <> showDefault <> value Scripts)

progParser :: ParserInfo (FilePath, Mode)
progParser =
    let p = (,) <$> pathParser <*> modeParser
    in info
        (p <**> helper)
        (fullDesc
        <> progDesc "Run a number of emulator traces and write all validator scripts and/or partial transactions to SCRIPT_PATH"
        <> header "plutus-use-cases-scripts - extract applied validators and partial transactions from emulator traces"
        )

main :: IO ()
main = execParser progParser >>= uncurry writeScripts

writeScripts :: FilePath -> Mode -> IO ()
writeScripts fp mode = do
    putStrLn $ "Writing " <> writeWhat mode <> " to: " <> fp
    traverse_ (uncurry3 (writeScriptsTo mode fp))
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

{-| Run an emulator trace and write the applied scripts to a file in Flat format
    using the name as a prefix.
-}
writeScriptsTo
    :: Mode
    -> FilePath
    -> String
    -> EmulatorTrace a
    -> EmulatorConfig
    -> IO ()
writeScriptsTo mode fp prefix trace emulatorCfg = do
    let (scriptEvents, balanceEvents) =
            S.fst'
            $ run
            $ foldEmulatorStreamM (L.generalize theFold)
            $ Trace.runEmulatorStream emulatorCfg def trace

    createDirectoryIfMissing True fp
    when (Scripts <= mode) $
        traverse_ (uncurry $ writeScript fp prefix) (zip [1::Int ..] (sveScript <$> scriptEvents))
    when (Transactions <= mode) $
        traverse_ (uncurry $ writeTransaction fp prefix) (zip [1::Int ..] balanceEvents)

{- There's an instance of Codec.Serialise for
    Script in Scripts.hs (see Note [Using Flat inside CBOR instance of Script]),
    which wraps Flat-encoded bytestings in CBOR, but that's not used here: we
    just use unwrapped Flat because that's more convenient for use with the
    `plc` command, for example.
-}
writeScript :: FilePath -> String -> Int -> Script -> IO ()
writeScript fp prefix idx script = do
    let filename = fp </> prefix <> "-" <> show idx <> ".flat"
    putStrLn $ "Writing script: " <> filename
    BSL.writeFile filename (BSL.fromStrict . flat . unScript $ script)

writeTransaction :: FilePath -> String -> Int -> UnbalancedTx -> IO ()
writeTransaction fp prefix idx tx = do
    let filename1 = fp </> prefix <> "-" <> show idx <> ".json"
    putStrLn $ "Writing partial transaction JSON: " <> filename1
    BSL.writeFile filename1 (encodePretty tx)
    case export tx of
        Left err -> putStrLn $ "Export tx failed for " <> filename1 <> ". Reason: " <> show (pretty err)
        Right exportTx -> do
            let filename2 = fp </> prefix <> "-" <> show idx <> ".cbor"
            putStrLn $ "Writing partial transaction CBOR: " <> filename2
            BSL.writeFile filename2 $ BSL.fromStrict (Binary.serialize' exportTx)

-- | `uncurry3` converts a curried function to a function on triples.
uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

theFold :: Folds.EmulatorEventFold ([ScriptValidationEvent], [UnbalancedTx])
theFold = (,) <$> Folds.scriptEvents <*> Folds.walletTxBalanceEvents

-- | Partial transaction that can be balanced by the wallet backend.
data ExportTx =
        ExportTx
            { partialTx   :: C.Tx C.AlonzoEra -- ^ The transaction itself
            , lookups     :: [(C.TxIn, C.TxOut C.AlonzoEra)] -- ^ The tx outputs for all inputs spent by the partial tx
            , signatories :: [C.Hash C.PaymentKey] -- ^ Key(s) that we expect to be used for balancing & signing. (Advisory)
            }
    deriving stock (Generic, Typeable)

instance Binary.ToCBOR ExportTx where
    toCBOR ExportTx{partialTx, lookups, signatories} =
        Binary.toCBOR
            -- This is the best I could do, the types in Cardano.API all seem to have different serialisation
            -- formats (ToCBOR, SerialiseAsCBOR, ToJSON)
            ( C.serialiseToCBOR partialTx
            , Aeson.encode lookups -- TODO: Missing CBOR instance(s) for TxOut AlonzoEra :(
            , Binary.serialize' signatories
            )

    encodedSizeExpr size _ =
        Binary.encodedSizeExpr
            size
            (Proxy @(Binary.LengthOf BSL.ByteString, Binary.LengthOf BSL.ByteString, Binary.LengthOf BSL.ByteString))

instance C.HasTypeProxy ExportTx where
    data AsType ExportTx = AsExportTx
    proxyToAsType _ = AsExportTx

export :: UnbalancedTx -> Either CardanoAPI.ToCardanoError ExportTx
export UnbalancedTx{unBalancedTxTx, unBalancedTxUtxoIndex, unBalancedTxRequiredSignatories} =
    ExportTx
        <$> mkTx unBalancedTxTx
        <*> mkLookups unBalancedTxUtxoIndex
        <*> mkSignatories unBalancedTxRequiredSignatories

mkTx :: Plutus.Tx -> Either CardanoAPI.ToCardanoError (C.Tx C.AlonzoEra)
mkTx = fmap (C.makeSignedTransaction []) . CardanoAPI.toCardanoTxBody

mkLookups :: Map Plutus.TxOutRef Plutus.TxOut -> Either CardanoAPI.ToCardanoError [(C.TxIn, C.TxOut C.AlonzoEra)]
mkLookups = traverse (bitraverse CardanoAPI.toCardanoTxIn CardanoAPI.toCardanoTxOut) . Map.toList

mkSignatories :: Set Plutus.PubKeyHash -> Either CardanoAPI.ToCardanoError [C.Hash C.PaymentKey]
mkSignatories = traverse CardanoAPI.toCardanoPaymentKeyHash . Set.toList
