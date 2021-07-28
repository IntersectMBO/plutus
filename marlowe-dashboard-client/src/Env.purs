module Env
  ( Env
  , DataProvider(..)
  ) where

import Prelude
import Effect.AVar (AVar)
import Halogen (SubscriptionId)
import Plutus.PAB.Webserver (SPParams_)
import Servant.PureScript.Settings (SPSettings_)

-- Application enviroment configuration
type Env
  = { ajaxSettings :: SPSettings_ SPParams_
    -- This AVar helps to solve a concurrency problem in the contract carousel subscriptions.
    -- See notes in [Contract.State(unsubscribeFromSelectCenteredStep)]
    -- There are two reasons why this is stored in the `Env` rather than the Contract.State:
    -- 1. There are multiple Contract.State (one per each contract) but only one carousel at a time.
    --    Sharing the subscription makes sense in that regard.
    -- 2. We need to be inside the Effect/Aff monad in order to create an AVar, and most of the state
    --    creation functions didn't require that, so it seemed wrong to lift several functions into Effect.
    --    In contrast, the Env is created in Main, where we already have access to Effect
    , contractStepCarouselSubscription :: AVar SubscriptionId
    , dataProvider :: DataProvider
    }

-- The frontend app can be run with two different data providers: the Marlowe PAB (the PAB bundled
-- up with the Marlowe Plutus contracts in one executable), or with the browser's localStorage
-- giving the local illusion of persistent and shared data. How this env property is set determines
-- the implementation of the functions in the ManageMarlowe capability monad.
data DataProvider
  = MarlowePAB
  | LocalStorage

derive instance eqDataProvider :: Eq DataProvider
