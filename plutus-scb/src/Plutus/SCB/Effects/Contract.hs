{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeOperators    #-}
module Plutus.SCB.Effects.Contract(
    ContractCommand(..),
    ContractEffect(..),
    invokeContract
    ) where

import           Control.Monad.Freer.TH (makeEffect)
import qualified Data.Aeson             as JSON

import           Plutus.SCB.Types       (PartiallyDecodedResponse)

-- | Commands to update a contract. 't' identifies the contract.
data ContractCommand t
    = InitContract t
    | UpdateContract t JSON.Value
    deriving (Show, Eq)

data ContractEffect t r where
    InvokeContract :: ContractCommand t -> ContractEffect  t PartiallyDecodedResponse
makeEffect ''ContractEffect
