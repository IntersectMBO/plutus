{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE OverloadedLabels     #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.Plutus.Contract.Request where

import qualified Data.Aeson                         as Aeson
import           Data.Row

import           Language.Plutus.Contract.Resumable
import           Language.Plutus.Contract.Schema    (Event (..), Handlers (..), Input, Output)
import qualified Language.Plutus.Contract.Schema    as Events

-- | @Contract s a@ is a contract with schema 's', producing a value of
--  type 'a'. See note [Contract Schema].
--
type Contract s a = Resumable (Step (Maybe (Event s)) (Handlers s)) a

-- | Constraints on the contract schema, ensuring that the requests produced
--   by the contracts are 'Monoid's (so that we can produce a record with
--   requests from different branches) and that the labels of the schema are
--   unique.
type ContractRow s =
  ( Forall (Output s) Monoid
  , Forall (Output s) Semigroup
  , AllUniqueLabels (Input s)
  , AllUniqueLabels (Output s)
  )

-- | Given a schema @s@ with an entry @l .== (resp, req)@, @request r@
--   is a contract that writes the request @r@ and waits for a response of type
--   @resp@.
request
  :: forall l req resp s.
    ( KnownSymbol l
    , HasType l resp (Input s)
    , HasType l req (Output s)
    , ContractRow s
    )
    => req
    -> Contract s resp
request out = CStep (Step go) where
  upd = Left $ Events.initialise @s @l out
  go Nothing = upd
  go (Just (Event rho)) = case trial rho (Label @l) of
    Left resp -> Right resp
    _         -> upd

-- | Write a request repeatedly until the desired response is returned.
requestMaybe
  :: forall l req resp s a.
     ( KnownSymbol l
     , HasType l resp (Input s)
     , HasType l req (Output s)
     , ContractRow s
     )
    => req
    -> (resp -> Maybe a)
    -> Contract s a
requestMaybe out check = do
  rsp <- request @l @req @resp @s out
  case check rsp of
    Nothing -> requestMaybe @l @req @resp @s out check
    Just a  -> pure a

-- | @select@ returns the contract that finished first, discarding the other
--   one.
--
select :: forall s a. Contract s a -> Contract s a -> Contract s a
select = CAlt

cJSONCheckpoint :: forall s a. (Aeson.FromJSON a, Aeson.ToJSON a) => Contract s a -> Contract s a
cJSONCheckpoint = CJSONCheckpoint
