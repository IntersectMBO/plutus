module AjaxUtils where

import Bootstrap
  ( alertDanger_
  )
import Control.Monad.Except
  ( ExceptT
  , runExceptT
  )
import Control.Monad.Reader
  ( class MonadAsk
  , ReaderT
  , ask
  , runReaderT
  )
import Control.Monad.State
  ( class MonadState
  )
import Data.Lens
  ( Lens'
  , assign
  )
import Halogen.HTML
  ( HTML
  , br_
  , div_
  , text
  )
import Network.RemoteData
  ( RemoteData(..)
  , fromEither
  )
import Prelude
  ( discard
  , bind
  , pure
  , ($)
  , (<>)
  , (>>>)
  )
import Servant.PureScript.Ajax
  ( AjaxError
  , ErrorDescription
      ( ConnectionError
      , DecodingError
      , ResponseFormatError
      )
  , runAjaxError
  )

showAjaxError ::
  forall p i.
  AjaxError ->
  HTML p i
showAjaxError = runAjaxError >>> _.description >>> showErrorDescription

showErrorDescription ::
  forall p i.
  ErrorDescription ->
  HTML p i
showErrorDescription (ResponseFormatError err) = text $ "ResponseFormatError: " <> err
showErrorDescription (DecodingError err) = text $ "DecodingError: " <> err
showErrorDescription (ConnectionError err) = text $ "ConnectionError: " <> err

ajaxErrorPane ::
  forall p i.
  AjaxError ->
  HTML p i
ajaxErrorPane error = div_ [ alertDanger_ [ showAjaxError error
                                          , br_
                                          , text "Please try again or contact support for assistance."
                                          ]
                           ]

runAjax ::
  forall m env a e.
  MonadAsk env m =>
  ReaderT env (ExceptT e m) a ->
  m (RemoteData e a)
runAjax action = do
  settings <- ask
  result <- runExceptT $ runReaderT action settings
  pure $ fromEither result

-- | Run an Ajax action, tracking its state and result into the target lens.
runAjaxTo ::
  forall m a e env state.
  MonadState state m =>
  MonadAsk env m =>
  Lens' state (RemoteData e a) ->
  ReaderT env (ExceptT e m) a ->
  m (RemoteData e a)
runAjaxTo lens action = do
  assign lens Loading
  result <- runAjax action
  assign lens result
  pure result
