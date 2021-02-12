{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Dataset ( contractsWithNames
               , contractsWithIndices
               ) where

import           Control.Monad.Trans.Except
import           Data.Bifunctor                                        (second)
import           Data.Either                                           (fromRight)
import           Data.Text                                             (Text)

import qualified Language.Marlowe                                      as Marlowe
import           Language.Plutus.Contract.Trace
import           Language.PlutusCore                                   (DefaultFun (..), runQuoteT)
import           Language.PlutusCore.Universe
import qualified Language.PlutusTx.Coordination.Contracts.Crowdfunding as Crowdfunding
import qualified Language.PlutusTx.Coordination.Contracts.Escrow       as Escrow
import qualified Language.PlutusTx.Coordination.Contracts.Future       as Future
import qualified Language.PlutusTx.Coordination.Contracts.Game         as Game
import qualified Language.PlutusTx.Coordination.Contracts.Vesting      as Vesting
import           Language.UntypedPlutusCore
import qualified Ledger                                                as Ledger
import qualified Ledger.Ada                                            as Ada
import           Ledger.Crypto
import qualified Ledger.Scripts                                        as Plutus
import qualified Ledger.Typed.Scripts                                  as Plutus
import           Ledger.Value

wallet1, wallet2 :: Wallet
wallet1 = Wallet 1
wallet2 = Wallet 2

escrowParams :: Escrow.EscrowParams d
escrowParams =
  Escrow.EscrowParams
    { Escrow.escrowDeadline = 200
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
            Vesting.VestingTranche (Ledger.Slot 10) (Ada.lovelaceValueOf 20)
        , Vesting.vestingTranche2 =
            Vesting.VestingTranche (Ledger.Slot 20) (Ada.lovelaceValueOf 40)
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
    Future.ftDeliveryDate  = Ledger.Slot 100,
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
  [ ("game-names", Game.gameValidator)
  , ("crowdfunding-names", Crowdfunding.contributionScript Crowdfunding.theCampaign)
  , ("marlowe-names", Plutus.validatorScript $ Marlowe.scriptInstance Marlowe.defaultMarloweParams)
  , ("vesting-names", Vesting.vestingScript vesting)
  , ("escrow-names", Plutus.validatorScript $ Escrow.scriptInstance escrowParams)
  , ("future-names", Future.validator theFuture Future.testAccounts) ]

contractsWithIndices ::
  [ (Text, Term DeBruijn DefaultUni DefaultFun ()) ]
contractsWithIndices = map (second (getTerm . Plutus.unScript . Plutus.unValidatorScript))
  [ ("game-indices", Game.gameValidator)
  , ("crowdfunding-indices", Crowdfunding.contributionScript Crowdfunding.theCampaign)
  , ("marlowe-indices", Plutus.validatorScript $ Marlowe.scriptInstance Marlowe.defaultMarloweParams)
  , ("vesting-indices", Vesting.vestingScript vesting)
  , ("escrow-indices", Plutus.validatorScript $ Escrow.scriptInstance escrowParams)
  , ("future-indices", Future.validator theFuture Future.testAccounts) ]
