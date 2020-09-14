module Language.Javascript.Monaco where

import Prelude
import Data.Maybe (Maybe(..))
import Halogen (RefLabel(..))
import Halogen.Monaco (Settings)
import Monaco (Editor, LanguageExtensionPoint(..))

languageExtensionPoint :: LanguageExtensionPoint
languageExtensionPoint = LanguageExtensionPoint { id: "typescript" }

refLabel :: RefLabel
refLabel = RefLabel "jsEditor"

settings :: forall m. (Editor -> m Unit) -> Settings m
settings setup =
  { languageExtensionPoint
  , theme: Nothing
  , monarchTokensProvider: Nothing
  , tokensProvider: Nothing
  , hoverProvider: Nothing
  , completionItemProvider: Nothing
  , codeActionProvider: Nothing
  , documentFormattingEditProvider: Nothing
  , refLabel
  , owner: "jsEditor"
  , setup
  }
