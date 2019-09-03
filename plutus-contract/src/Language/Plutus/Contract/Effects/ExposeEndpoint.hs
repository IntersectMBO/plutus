{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.ExposeEndpoint where

import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.Proxy
import           Data.Row
import           Data.Set                         (Set)
import qualified Data.Set                         as Set
import           GHC.Generics                     (Generic)
import           GHC.TypeLits                     (Symbol, symbolVal)

import           Language.Plutus.Contract.IOTS
import           Language.Plutus.Contract.Request as Req
import           Language.Plutus.Contract.Schema  (Event (..), Handlers (..), Input, Output)

newtype EndpointDescription = EndpointDescription { getEndpointDescription :: String }
    deriving stock (Eq, Ord, Generic, Show)
    deriving newtype (ToJSON, FromJSON)
    deriving anyclass (IotsType)

type HasEndpoint l a s =
  ( HasType l a (Input s)
  , HasType l ActiveEndpoints (Output s)
  , KnownSymbol l
  , ContractRow s
  )

newtype ActiveEndpoints = ActiveEndpoints { unActiveEndpoints :: Set EndpointDescription }
  deriving (Eq, Ord, Show)
  deriving newtype (Semigroup, Monoid, ToJSON, FromJSON)

type Endpoint l a = l .== (a, ActiveEndpoints)

-- | Expose an endpoint, return the data that was entered
endpoint
  :: forall l a s.
     ( HasEndpoint l a s )
  => Contract s a
endpoint = request @l @_ @_ @s s where
  s = ActiveEndpoints $ Set.singleton $ EndpointDescription $ symbolVal (Proxy @l)

event
  :: forall (l :: Symbol) a s. (KnownSymbol l, HasType l a (Input s), AllUniqueLabels (Input s))
  => a
  -> Event s
event = Event . IsJust (Label @l)

isActive
  :: forall (l :: Symbol) s. (KnownSymbol l, HasType l ActiveEndpoints (Output s))
  => Handlers s
  -> Bool
isActive (Handlers r) =
  let lbl = EndpointDescription $ symbolVal (Proxy @l)
  in Set.member lbl $ unActiveEndpoints $ r .! Label @l
