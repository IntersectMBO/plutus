module Clipboard
  ( class MonadClipboard
  , handleAction
  , Action(..)
  , copy
  , clipboardButton
  , showShortCopyLong
  ) where

import Bootstrap (btn, btnLink, displayFlex, textTruncate)
import Control.Monad (class Monad)
import Control.Monad.Reader.Trans (ReaderT)
import Control.Monad.State.Trans (StateT)
import Control.Monad.Trans.Class (lift)
import Data.Function ((<<<))
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Uncurried (EffectFn1, runEffectFn1)
import Halogen (HalogenM)
import Halogen.HTML (ClassName(..), HTML, button, div, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import Icons (Icon(..), icon)
import Prelude (class Show, Unit, const, ($))

data Action
  = CopyToClipboard String

derive instance genericAction :: Generic Action _

instance showAction :: Show Action where
  show = genericShow

class MonadClipboard m where
  copy :: String -> m Unit

instance monadClipboardEffect :: MonadClipboard Effect where
  copy = runEffectFn1 _copy

instance monadClipboardAff :: MonadClipboard Aff where
  copy = liftEffect <<< copy

instance monadClipboardHalogenM :: (Monad m, MonadClipboard m) => MonadClipboard (HalogenM state action slots output m) where
  copy = lift <<< copy

instance monadClipboardStateT :: (Monad m, MonadClipboard m) => MonadClipboard (StateT s m) where
  copy = lift <<< copy

instance monadClipboardReaderT :: (Monad m, MonadClipboard m) => MonadClipboard (ReaderT env m) where
  copy = lift <<< copy

handleAction :: forall m. MonadClipboard m => Action -> m Unit
handleAction (CopyToClipboard str) = copy str

foreign import _copy :: EffectFn1 String Unit

clipboardButton :: forall p. String -> HTML p Action
clipboardButton str =
  div
    [ class_ $ ClassName "clipboard" ]
    [ button
        [ classes [ btn, btnLink ]
        , onClick $ const $ Just $ CopyToClipboard str
        ]
        [ icon Clipboard ]
    ]

showShortCopyLong :: forall p. String -> Maybe (Array (HTML p Action)) -> HTML p Action
showShortCopyLong str content =
  div [ class_ displayFlex ]
    [ div [ classes [ textTruncate ] ]
        (fromMaybe [ text str ] content)
    , clipboardButton str
    ]
