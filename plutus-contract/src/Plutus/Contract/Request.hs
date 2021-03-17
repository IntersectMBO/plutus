{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
module Plutus.Contract.Request(
  ContractRow
  , request
  , requestMaybe
  ) where

import           Control.Applicative
import           Control.Lens              (review)
import qualified Control.Monad.Freer.Error as E
import           Data.Row
import           Data.Text.Extras          (tshow)

import           Plutus.Contract.Schema    (Event (..), Handlers (..), Input, Output)
import qualified Plutus.Contract.Schema    as Events

import           Plutus.Contract.Resumable
import           Plutus.Contract.Types

import           Prelude                   as Haskell

-- | Constraints on the contract schema, ensuring that the requests produced
--   by the contracts are 'Monoid's (so that we can produce a record with
--   requests from different branches) and that the labels of the schema are
--   unique.
type ContractRow s =
  ( AllUniqueLabels (Input s)
  , AllUniqueLabels (Output s)
  )

-- | Given a schema @s@ with an entry @l .== (resp, req)@, @request r@
--   is a contract that writes the request @r@ and waits for a response of type
--   @resp@.
request
  :: forall w l req resp s e.
    ( KnownSymbol l
    , HasType l resp (Input s)
    , HasType l req (Output s)
    , AsContractError e
    )
    => req
    -> Contract w s e resp
request out = Contract $ do
  Event rho <- prompt @(Event s) @(Handlers s) (Events.initialise @s @l out)
  case trial' rho (Label @l) of
    Just v  -> pure v
    Nothing -> E.throwError @e (review _ResumableError $ WrongVariantError $ "Expected: " <> tshow (Label @l))

-- | Write a request repeatedly until the desired response is returned.
requestMaybe
  :: forall w l req resp s a e.
     ( KnownSymbol l
     , HasType l resp (Input s)
     , HasType l req (Output s)
     , ContractRow s
    , AsContractError e
     )
    => req
    -> (resp -> Maybe a)
    -> Contract w s e a
requestMaybe out check = do
  rsp <- request @w @l @req @resp @s out
  case check rsp of
    Nothing -> requestMaybe @w @l @req @resp @s out check
    Just a  -> pure a
