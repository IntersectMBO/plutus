{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
module Language.Plutus.Contract.Prompt.Hooks(
    -- * Hooks
      Hook(..)
    , txHook
    , addrHook
    , slotHook
    , endpointHook
    -- * Data about outstanding requests
    , Hooks(..)
    , hooks
    , transactions
    , activeEndpoints
    , addresses
    , nextSlot
    ) where

import           Control.Lens
import qualified Data.Aeson                  as Aeson
import           Data.Semigroup              (Min (..))
import           Data.Sequence               (Seq)
import qualified Data.Sequence               as Seq
import           Data.Set                    (Set)
import qualified Data.Set                    as Set
import           GHC.Generics                (Generic)

import           Language.Plutus.Contract.Tx (UnbalancedTx)
import           Ledger.Slot                 (Slot (..))
import           Ledger.Tx                   (Address)

-- | A condition that the contract is waiting for. See note [Hooks and Events]
--   in 'Language.Plutus.Contract.Effects'.
data Hook a =
    TxHook UnbalancedTx
    | AddrHook Address
    | SlotHook Slot
    | EndpointHook String a -- a is the schema. In the future it will be a type-level Map Symbol GraphQLSchema or whatever (the Symbol being the endpoint name), and the String parameter can go.
    deriving stock (Eq, Show, Generic, Functor)
    deriving anyclass (Aeson.FromJSON, Aeson.ToJSON)

makePrisms ''Hook

txHook :: UnbalancedTx -> Hook a
txHook = TxHook

addrHook :: Address -> Hook a
addrHook = AddrHook

slotHook :: Slot -> Hook a
slotHook = SlotHook

endpointHook :: String -> Hook ()
endpointHook s = EndpointHook s ()

newtype Hooks = Hooks { unHooks :: Seq (Hook ()) }
    deriving stock (Eq, Show, Generic)
    deriving newtype (Aeson.FromJSON, Aeson.ToJSON, Semigroup, Monoid)

transactions :: Hooks -> [UnbalancedTx]
transactions = toListOf (traversed . _TxHook) . unHooks

activeEndpoints :: Hooks -> Set String
activeEndpoints = Set.fromList . toListOf (traversed . _EndpointHook . _1) . unHooks

addresses :: Hooks -> Set Address
addresses = Set.fromList . toListOf (traversed . _AddrHook) . unHooks

nextSlot :: Hooks -> Maybe Slot
nextSlot = fmap getMin . foldMapOf (traversed . _SlotHook) (Just . Min) . unHooks

hooks :: Hook () -> Hooks
hooks = Hooks . Seq.singleton
