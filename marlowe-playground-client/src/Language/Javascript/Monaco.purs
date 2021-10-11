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

settings :: forall m. Applicative m => (Editor -> m Unit) -> Settings m
settings setup =
  { languageExtensionPoint
  , theme: Nothing
  , monarchTokensProvider: pure Nothing
  , tokensProvider: pure Nothing
  , hoverProvider: pure Nothing
  , completionItemProvider: pure Nothing
  , codeActionProvider: pure Nothing
  , documentFormattingEditProvider: pure Nothing
  , refLabel
  , owner: "jsEditor"
  , setup
  }
