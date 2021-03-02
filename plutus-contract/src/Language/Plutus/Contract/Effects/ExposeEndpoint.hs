{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.ExposeEndpoint(
    HasEndpoint
    , Endpoint
    , ActiveEndpoint(..)
    , EndpointDescription(..)
    , EndpointValue(..)
    , endpoint
    , endpointWithMeta
    , endpointDescription
    , event
    , isActive
    ) where

import           Data.Aeson                       (FromJSON, ToJSON)
import qualified Data.Aeson                       as JSON
import           Data.Maybe                       (isJust)
import           Data.Proxy
import           Data.Row
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                     (Generic)
import           GHC.TypeLits                     (Symbol, symbolVal)

import           Language.Plutus.Contract.Request as Req
import           Language.Plutus.Contract.Schema  (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Types   (AsContractError, Contract)
import           Wallet.Types                     (EndpointDescription (..), EndpointValue (..))

type HasEndpoint l a s =
  ( HasType l (EndpointValue a) (Input s)
  , HasType l ActiveEndpoint (Output s)
  , KnownSymbol l
  , ContractRow s
  )

data ActiveEndpoint = ActiveEndpoint
  { aeDescription :: EndpointDescription -- ^ The name of the endpoint
  , aeMetadata    :: Maybe JSON.Value -- ^ Data that should be shown to the user
  }
  deriving (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

instance Pretty ActiveEndpoint where
  pretty ActiveEndpoint{aeDescription, aeMetadata} =
    indent 2 $ vsep
      [ "Endpoint:" <+> pretty aeDescription
      , "Metadata:" <+> viaShow aeMetadata
      ]

type Endpoint l a = l .== (EndpointValue a, ActiveEndpoint)

-- | Expose an endpoint, return the data that was entered
endpoint
  :: forall l a w s e.
     ( HasEndpoint l a s
     , AsContractError e
     )
  => Contract w s e a
endpoint = unEndpointValue <$> request @w @l @_ @_ @s s where
  s = ActiveEndpoint
        { aeDescription = EndpointDescription $ symbolVal (Proxy @l)
        , aeMetadata    = Nothing
        }

-- | Expose an endpoint with some metadata. Return the data that was entered.
endpointWithMeta
  :: forall l a w s e b.
     ( HasEndpoint l a s
     , AsContractError e
     , ToJSON b
     )
  => b
  -> Contract w s e a
endpointWithMeta b = unEndpointValue <$> request @w @l @_ @_ @s s where
  s = ActiveEndpoint
        { aeDescription = endpointDescription (Proxy @l)
        , aeMetadata    = Just $ JSON.toJSON b
        }

endpointDescription :: forall l. KnownSymbol l => Proxy l -> EndpointDescription
endpointDescription = EndpointDescription . symbolVal

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
