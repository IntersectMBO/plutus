{-# LANGUAGE NamedFieldPuns #-}

module SimulationUtils where

import           Ledger.Scripts        (ValidatorHash (ValidatorHash))
import           Ledger.Value          (CurrencySymbol (CurrencySymbol), TokenName, Value)
import qualified Ledger.Value          as Value
import           Playground.Types      (ContractCall (CallEndpoint), EndpointName, FunctionSchema (FunctionSchema),
                                        KnownCurrency (KnownCurrency), SimulatorAction,
                                        SimulatorWallet (SimulatorWallet), argumentValues, arguments, caller,
                                        endpointName, hash, knownTokens, simulatorWalletBalance, simulatorWalletWallet)
import           Schema                (ToArgument, toArgument)
import           Wallet.Emulator.Types (Wallet)

callEndpoint :: ToArgument a => Wallet -> EndpointName -> a -> SimulatorAction
callEndpoint caller endpointName param =
    CallEndpoint
        { caller
        , argumentValues =
              FunctionSchema {endpointName, arguments = [toArgument param]}
        }

initialBalance :: [KnownCurrency] -> Integer -> Value
initialBalance currencies balance = foldMap withCurrencies currencies
  where
    withCurrencies :: KnownCurrency -> Value
    withCurrencies KnownCurrency {hash = ValidatorHash hash, knownTokens} =
        foldMap withTokens knownTokens
      where
        currencySymbol = CurrencySymbol hash
        withTokens :: TokenName -> Value
        withTokens tokenName = Value.singleton currencySymbol tokenName balance

simulatorWallet :: [KnownCurrency] -> Integer -> Wallet -> SimulatorWallet
simulatorWallet currencies balance wallet =
    SimulatorWallet
        { simulatorWalletWallet = wallet
        , simulatorWalletBalance = initialBalance currencies balance
        }
