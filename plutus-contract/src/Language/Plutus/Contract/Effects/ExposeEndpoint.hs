{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingVia         #-}
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
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Extras
import           GHC.Generics                     (Generic)
import           GHC.TypeLits                     (Symbol, symbolVal)

import           Language.Plutus.Contract.IOTS
import           Language.Plutus.Contract.Request as Req
import           Language.Plutus.Contract.Schema  (Event (..), Handlers (..), Input, Output)

newtype EndpointDescription = EndpointDescription { getEndpointDescription :: String }
    deriving stock (Eq, Ord, Generic, Show)
    deriving newtype (ToJSON, FromJSON)
    deriving anyclass (IotsType)
    deriving Pretty via (Tagged "ExposeEndpoint:" String)

newtype EndpointValue a = EndpointValue { unEndpointValue :: a }
    deriving stock (Eq, Ord, Generic, Show)
    deriving newtype (ToJSON, FromJSON)
    deriving anyclass (IotsType)

deriving via (Tagged "EndpointValue:" (PrettyShow a)) instance (Show a => Pretty (EndpointValue a))

type HasEndpoint l a s =
  ( HasType l (EndpointValue a) (Input s)
  , HasType l ActiveEndpoints (Output s)
  , KnownSymbol l
  , ContractRow s
  )

newtype ActiveEndpoints = ActiveEndpoints { unActiveEndpoints :: Set EndpointDescription }
  deriving (Eq, Ord, Show, Generic)
  deriving newtype (Semigroup, Monoid, ToJSON, FromJSON)
  deriving Pretty via (PrettyFoldable Set EndpointDescription)

type Endpoint l a = l .== (EndpointValue a, ActiveEndpoints)

-- | Expose an endpoint, return the data that was entered
endpoint
  :: forall l a s e.
     ( HasEndpoint l a s )
  => Contract s e a
endpoint = unEndpointValue <$> request @l @_ @_ @s s where
  s = ActiveEndpoints $ Set.singleton $ EndpointDescription $ symbolVal (Proxy @l)

event
  :: forall (l :: Symbol) a s. (KnownSymbol l, HasType l (EndpointValue a) (Input s), AllUniqueLabels (Input s))
  => a
  -> Event s
event = Event . IsJust (Label @l) . EndpointValue

isActive
  :: forall (l :: Symbol) s. (KnownSymbol l, HasType l ActiveEndpoints (Output s))
  => Handlers s
  -> Bool
isActive (Handlers r) =
  let lbl = EndpointDescription $ symbolVal (Proxy @l)
  in Set.member lbl $ unActiveEndpoints $ r .! Label @l
