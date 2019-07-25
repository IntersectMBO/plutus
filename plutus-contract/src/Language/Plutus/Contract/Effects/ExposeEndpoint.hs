{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
-- | Expose an endpoint
module Language.Plutus.Contract.Effects.ExposeEndpoint where

import           Control.Eff
import           Control.Eff.Exception
import           Control.Eff.Extend
import           Control.Eff.Reader.Lazy
import           Data.Aeson                            (FromJSON)
import qualified Data.Aeson                            as Aeson
import           Data.Function                         (fix)


import           Language.Plutus.Contract.Prompt.Event as Event
import           Language.Plutus.Contract.Prompt.Hooks as Hooks

data ExposeEndpoint v where
  ExposeEndpoint :: FromJSON a => String -> ExposeEndpoint a

-- TODO: The name of the endpoint (currently a value) and its schema (currently
-- missing from the ExposeEndpoint type) should both be expressed on the type
-- level, so that we can write
--
-- endpoint :: Member (ExposeEndpoint "myEndpoint" MySchema) r => Eff r (Result MySchema)
-- (maybe we don't need the endpoint name then, if we say that each endpoint
-- has a unique type)

exposeEndpoint :: FromJSON a => Member ExposeEndpoint r => String -> Eff r a
exposeEndpoint = send . ExposeEndpoint

instance (Member (Reader (Maybe Event)) r, Member (Exc (Hook ())) r, Member (Exc String) r) => Handle ExposeEndpoint r a k where
  handle step cor req = case req of
    ExposeEndpoint ep -> step (comp (singleK promptEndpoint) cor ^$ ep)

promptEndpoint :: (FromJSON a, Member (Reader (Maybe Event)) r, Member (Exc (Hook ())) r, Member (Exc String) r) => String -> Eff r a
promptEndpoint ep = do
  sl <- reader (>>= Event.endpointEvent)
  case sl of
    Just (ep', vl)
      | ep' == ep ->
        case Aeson.fromJSON vl of
                    Aeson.Success r   -> pure r
                    Aeson.Error   err -> throwError @String err
    _ -> throwError @(Hook ()) (Hooks.endpointHook ep)

runExposeEndpoint :: (Member (Reader (Maybe Event)) r, Member (Exc (Hook ())) r, Member (Exc String) r) => Eff (ExposeEndpoint ': r) a -> Eff r a
runExposeEndpoint = fix (handle_relay pure)
