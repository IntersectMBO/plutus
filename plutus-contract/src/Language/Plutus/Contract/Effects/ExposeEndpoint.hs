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
import           Data.Maybe                       (isJust)
import           Data.Proxy
import           Data.Row
import           Data.String                      (IsString)
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Extras
import           GHC.Generics                     (Generic)
import           GHC.TypeLits                     (Symbol, symbolVal)

import qualified Language.Haskell.TH.Syntax       as TH
import           Language.Plutus.Contract.IOTS
import           Language.Plutus.Contract.Request as Req
import           Language.Plutus.Contract.Schema  (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Types   (AsContractError, Contract)

newtype EndpointDescription = EndpointDescription { getEndpointDescription :: String }
    deriving stock (Eq, Ord, Generic, Show, TH.Lift)
    deriving newtype (IsString)
    deriving anyclass (ToJSON, FromJSON, IotsType)
    deriving Pretty via (Tagged "ExposeEndpoint:" String)

newtype EndpointValue a = EndpointValue { unEndpointValue :: a }
    deriving stock (Eq, Ord, Generic, Show)
    deriving anyclass (ToJSON, FromJSON, IotsType)

deriving via (Tagged "EndpointValue:" (PrettyShow a)) instance (Show a => Pretty (EndpointValue a))

type HasEndpoint l a s =
  ( HasType l (EndpointValue a) (Input s)
  , HasType l ActiveEndpoint (Output s)
  , KnownSymbol l
  , ContractRow s
  )

newtype ActiveEndpoint = ActiveEndpoint { unActiveEndpoints :: EndpointDescription }
  deriving (Eq, Ord, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)
  deriving Pretty via (Tagged "ActiveEndpoint:" EndpointDescription)

type Endpoint l a = l .== (EndpointValue a, ActiveEndpoint)

-- | Expose an endpoint, return the data that was entered
endpoint
  :: forall l a s e.
     ( HasEndpoint l a s
     , AsContractError e
     )
  => Contract s e a
endpoint = unEndpointValue <$> request @l @_ @_ @s s where
  s = ActiveEndpoint $ EndpointDescription $ symbolVal (Proxy @l)

event
  :: forall (l :: Symbol) a s. (KnownSymbol l, HasType l (EndpointValue a) (Input s), AllUniqueLabels (Input s))
  => a
  -> Event s
event = Event . IsJust (Label @l) . EndpointValue

isActive
  :: forall (l :: Symbol) s. (KnownSymbol l, HasType l ActiveEndpoint (Output s))
  => Handlers s
  -> Bool
isActive (Handlers r) = isJust $ trial' r (Label @l)
