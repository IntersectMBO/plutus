{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Dataset ( contractsWithNames
               , contractsWithIndices
               ) where

import           Control.Monad.Trans.Except
import           Data.Bifunctor                    (second)
import           Data.Either                       (fromRight)
import           Data.Text                         (Text)

import qualified Language.Marlowe                  as Marlowe
import qualified Ledger
import qualified Ledger.Ada                        as Ada
import           Ledger.Crypto
import qualified Ledger.Scripts                    as Plutus
import qualified Ledger.TimeSlot                   as TimeSlot
import qualified Ledger.Typed.Scripts              as Plutus
import           Ledger.Value
import           Plutus.Contract.Trace
import qualified Plutus.Contracts.Crowdfunding     as Crowdfunding
import qualified Plutus.Contracts.Escrow           as Escrow
import qualified Plutus.Contracts.Future           as Future
import qualified Plutus.Contracts.GameStateMachine as GameStateMachine
import qualified Plutus.Contracts.Vesting          as Vesting
import           PlutusCore                        (runQuoteT)
import           PlutusCore.Default
import           UntypedPlutusCore

wallet1, wallet2 :: Wallet
wallet1 = Wallet 1
wallet2 = Wallet 2

escrowParams :: Escrow.EscrowParams d
escrowParams =
  Escrow.EscrowParams
    { Escrow.escrowDeadline = TimeSlot.slotToPOSIXTime 200
    , Escrow.escrowTargets  =
        [ Escrow.payToPubKeyTarget (pubKeyHash $ walletPubKey wallet1)
                                   (Ada.lovelaceValueOf 10)
        , Escrow.payToPubKeyTarget (pubKeyHash $ walletPubKey wallet2)
                                   (Ada.lovelaceValueOf 20)
        ]
    }

vesting :: Vesting.VestingParams
vesting =
    Vesting.VestingParams
        { Vesting.vestingTranche1 =
            Vesting.VestingTranche (TimeSlot.slotToPOSIXTime 10) (Ada.lovelaceValueOf 20)
        , Vesting.vestingTranche2 =
            Vesting.VestingTranche (TimeSlot.slotToPOSIXTime 20) (Ada.lovelaceValueOf 40)
        , Vesting.vestingOwner    = Ledger.pubKeyHash $ walletPubKey wallet1 }

-- Future data
forwardPrice :: Value
forwardPrice = Ada.lovelaceValueOf 1123

penalty :: Value
penalty = Ada.lovelaceValueOf 1000

units :: Integer
units = 187

oracleKeys :: (PrivateKey, PubKey)
oracleKeys =
    let wllt = Wallet 10 in
        (walletPrivKey wllt, walletPubKey wllt)

theFuture :: Future.Future
theFuture = Future.Future {
    Future.ftDeliveryDate  = TimeSlot.slotToPOSIXTime 100,
    Future.ftUnits         = units,
    Future.ftUnitPrice     = forwardPrice,
    Future.ftInitialMargin = Ada.lovelaceValueOf 800,
    Future.ftPriceOracle   = snd oracleKeys,
    Future.ftMarginPenalty = penalty
    }

-- Plutus contracts
getTerm
  :: Program name uni fun att
  -> Term name uni fun att
getTerm (Program _ _ t) = t

nameDeBruijn
  :: Term DeBruijn DefaultUni DefaultFun ()
  -> Term NamedDeBruijn DefaultUni DefaultFun ()
nameDeBruijn = termMapNames (\(DeBruijn ix) -> NamedDeBruijn "" ix)

runQuote
  :: Term NamedDeBruijn DefaultUni DefaultFun ()
  -> Term Name DefaultUni DefaultFun ()
runQuote tm = do
  (fromRight $ error "Failed to assign names to terms")
    . runExcept @FreeVariableError . runQuoteT $ unDeBruijnTerm tm

contractsWithNames :: [ (Text, Term Name DefaultUni DefaultFun ()) ]
contractsWithNames = map (second (runQuote . nameDeBruijn . getTerm . Plutus.unScript . Plutus.unValidatorScript))
  [ ("game-names", Plutus.validatorScript GameStateMachine.typedValidator)
  , ("crowdfunding-names", Crowdfunding.contributionScript Crowdfunding.theCampaign)
  , ("marlowe-names", Plutus.validatorScript $ Marlowe.typedValidator Marlowe.defaultMarloweParams)
  , ("vesting-names", Vesting.vestingScript vesting)
  , ("escrow-names", Plutus.validatorScript $ Escrow.typedValidator escrowParams)
  , ("future-names", Future.validator theFuture Future.testAccounts) ]

contractsWithIndices ::
  [ (Text, Term DeBruijn DefaultUni DefaultFun ()) ]
contractsWithIndices = map (second (getTerm . Plutus.unScript . Plutus.unValidatorScript))
  [ ("game-indices", Plutus.validatorScript GameStateMachine.typedValidator)
  , ("crowdfunding-indices", Crowdfunding.contributionScript Crowdfunding.theCampaign)
  , ("marlowe-indices", Plutus.validatorScript $ Marlowe.typedValidator Marlowe.defaultMarloweParams)
  , ("vesting-indices", Vesting.vestingScript vesting)
  , ("escrow-indices", Plutus.validatorScript $ Escrow.typedValidator escrowParams)
  , ("future-indices", Future.validator theFuture Future.testAccounts) ]
