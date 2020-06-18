{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
module Language.Plutus.Contract.Trace.RequestHandler(
    RequestHandler(..)
    , tryHandler
    , wrapHandler
    , extract
    , maybeToHandler
    ) where

import           Control.Applicative                (Alternative (empty))
import           Control.Arrow                      (Kleisli (..))
import           Control.Lens
import           Control.Monad                      (foldM)
import           Control.Monad.Freer
import           Control.Monad.Freer.NonDet         (NonDet)
import qualified Control.Monad.Freer.NonDet         as NonDet
import           Data.Monoid                        (Alt (..), Ap (..))

import           Language.Plutus.Contract.Resumable (Request (..), Response (..))


-- | Request handlers that can choose whether to handle an effect (using
--   'Alternative'). This is useful if 'req' is a sum type.
newtype RequestHandler effs req resp = RequestHandler { unRequestHandler :: req -> Eff (NonDet ': effs) resp }
    deriving stock (Functor)
    deriving (Profunctor) via (Kleisli (Eff (NonDet ': effs)))
    deriving (Semigroup, Monoid) via (Ap ((->) req) (Alt (Eff (NonDet ': effs)) resp))


-- Try the handler on the requests until it succeeds for the first time, then stop.
tryHandler ::
    forall effs req resp
    . RequestHandler effs req resp
    -> [req]
    -> Eff effs (Maybe resp)
tryHandler (RequestHandler h) requests =
    foldM (\e i -> maybe (NonDet.makeChoiceA @Maybe $ h i) (pure . Just) e) Nothing requests

extract :: Alternative f => Prism' a b -> a -> f b
extract p = maybe empty pure . preview p

wrapHandler :: RequestHandler effs req resp -> RequestHandler effs (Request req) (Response resp)
wrapHandler (RequestHandler h) = RequestHandler $ \Request{rqID, itID, rqRequest} -> do
    r <- h rqRequest
    pure $ Response{rspRqID = rqID, rspResponse = r, rspItID = itID }

maybeToHandler :: (req -> Maybe resp) -> RequestHandler effs req resp
maybeToHandler f = RequestHandler $ maybe empty pure . f
