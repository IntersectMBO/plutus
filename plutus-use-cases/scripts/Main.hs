module Main(main) where

import qualified Control.Foldl                 as L
import           Control.Monad.Freer           (run)
import qualified Data.ByteString.Lazy          as BSL
import           Data.Foldable                 (traverse_)
import           Flat                          (flat)
import           Ledger.Index                  (ScriptValidationEvent (sveScript))
import           Plutus.Trace.Emulator         (EmulatorTrace)
import qualified Plutus.Trace.Emulator         as Trace
import           Plutus.V1.Ledger.Scripts      (Script (..))
import qualified Streaming.Prelude             as S
import           System.Directory              (createDirectoryIfMissing)
import           System.Environment            (getArgs)
import           System.FilePath               ((</>))
import qualified Wallet.Emulator.Folds         as Folds
import           Wallet.Emulator.Stream        (defaultEmulatorConfig, foldEmulatorStreamM)

import qualified Plutus.Contracts.Crowdfunding as Crowdfunding
import qualified Plutus.Contracts.Game         as Game
import           Spec.Auction                  as Auction
import qualified Spec.Currency                 as Currency
import qualified Spec.Escrow                   as Escrow
import qualified Spec.Future                   as Future
import qualified Spec.GameStateMachine         as GameStateMachine
import qualified Spec.MultiSig                 as MultiSig
import qualified Spec.MultiSigStateMachine     as MultiSigStateMachine
import qualified Spec.PingPong                 as PingPong
import qualified Spec.Prism                    as Prism
import qualified Spec.PubKey                   as PubKey
import qualified Spec.Stablecoin               as Stablecoin
import qualified Spec.TokenAccount             as TokenAccount
import qualified Spec.Vesting                  as Vesting

main :: IO ()
main = do
    args <- getArgs
    case args of
        [script_path] -> writeScripts script_path
        _             -> traverse_ putStrLn [
            "usage: plutus-use-cases-scripts SCRIPT_PATH",
            "Run a number of emulator traces and write all fully applied validator scripts to SCRIPT_PATH"
            ]

writeScripts :: FilePath -> IO ()
writeScripts fp = do
    putStrLn $ "Writing scripts to: " <> fp
    traverse_ (uncurry (writeScriptsTo fp))
        [ ("crowdfunding-success", Crowdfunding.successfulCampaign)
        , ("currency", Currency.currencyTrace)
        , ("escrow-redeem_1", Escrow.redeemTrace)
        , ("escrow-redeem_2", Escrow.redeem2Trace)
        , ("escrow-refund", Escrow.refundTrace)
        , ("future-increase-margin", Future.increaseMarginTrace)
        , ("future-settle-early", Future.settleEarlyTrace)
        , ("future-pay-out", Future.payOutTrace)
        , ("game-guess", Game.guessTrace)
        , ("game-guessWrong", Game.guessWrongTrace)
        , ("game-sm-success", GameStateMachine.successTrace)
        , ("game-sm-success_2", GameStateMachine.successTrace2)
        , ("multisig-success", MultiSig.succeedingTrace)
        , ("multisig-failure", MultiSig.failingTrace)
        , ("multisig-sm", MultiSigStateMachine.lockProposeSignPay 3 2)
        , ("ping-pong", PingPong.pingPongTrace)
        , ("ping-pong_2", PingPong.twoPartiesTrace)
        , ("prism", Prism.prismTrace)
        , ("pubkey", PubKey.pubKeyTrace)
        , ("stablecoin_1", Stablecoin.stablecoinTrace)
        , ("stablecoin_2", Stablecoin.maxReservesExceededTrace)
        , ("token-account", TokenAccount.tokenAccountTrace)
        , ("vesting", Vesting.retrieveFundsTrace)
        , ("auction_1", Auction.auctionTrace1)
        , ("auction_2", Auction.auctionTrace2)
        ]

{-| Run an emulator trace and write the applied scripts to a file in Flat format
    using the name as a prefix.  There's an instance of Codec.Serialise for
    Script in Scripts.hs (see Note [Using Flat inside CBOR instance of Script]),
    which wraps Flat-encoded bytestings in CBOR, but that's not used here: we
    just use unwrapped Flat because that's more convenient for use with the
    `plc` command, for example.
-}
writeScriptsTo :: FilePath -> String -> EmulatorTrace a -> IO ()
writeScriptsTo fp prefix trace = do
    let events =
            S.fst'
            $ run
            $ foldEmulatorStreamM (L.generalize Folds.scriptEvents)
            $ Trace.runEmulatorStream defaultEmulatorConfig trace
        writeScript idx script = do
            let filename = fp </> prefix <> "-" <> show idx <> ".flat"
            putStrLn $ "Writing script: " <> filename
            BSL.writeFile filename (BSL.fromStrict . flat . unScript $ script)
    createDirectoryIfMissing True fp
    traverse_ (uncurry writeScript) (zip [1::Int ..] (sveScript <$> events))
