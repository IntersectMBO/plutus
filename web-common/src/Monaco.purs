module Monaco where

import Prelude
import Data.Function.Uncurried (Fn1, Fn2, Fn5, runFn1, runFn2, runFn5)
import Data.Generic.Rep (class Generic)
import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.String.Regex (Regex)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple)
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, EffectFn4, runEffectFn1, runEffectFn2, runEffectFn3, runEffectFn4)
import Foreign (unsafeFromForeign, unsafeToForeign)
import Foreign.Generic (class Decode, class Encode, Foreign, SumEncoding(..), defaultOptions, encode, genericEncode)
import Foreign.Object (Object)
import Foreign.Object as Object
import Web.HTML (HTMLElement)

newtype LanguageExtensionPoint
  = LanguageExtensionPoint { id :: String }

_id :: Lens' LanguageExtensionPoint String
_id = _Newtype <<< prop (SProxy :: SProxy "id")

derive instance newtypeLanguageExtensionPoint :: Newtype LanguageExtensionPoint _

derive instance genericLanguageExtensionPoint :: Generic LanguageExtensionPoint _

derive newtype instance encodeLanguageExtensionPoint :: Encode LanguageExtensionPoint

newtype MonarchLanguageBracket
  = MonarchLanguageBracket { close :: String, open :: String, token :: String }

derive instance newtypeMonarchLanguageBracket :: Newtype MonarchLanguageBracket _

derive instance genericMonarchLanguageBracket :: Generic MonarchLanguageBracket _

derive newtype instance encodeMonarchLanguageBracket :: Encode MonarchLanguageBracket

data Action
  = Action { token :: String, next :: Maybe String, log :: Maybe String }
  | Cases { cases :: (Object String), log :: Maybe String }

derive instance genericAction :: Generic Action _

instance encodeAction :: Encode Action where
  encode a =
    let
      sumEncoding =
        TaggedObject
          { tagFieldName: "tag"
          , contentsFieldName: "contents"
          , constructorTagTransform: identity
          , unwrapRecords: true
          }
    in
      genericEncode (defaultOptions { sumEncoding = sumEncoding }) a

newtype LanguageRule
  = LanguageRule { regex :: Regex, action :: Action }

derive instance newtypeLanguageRule :: Newtype LanguageRule _

derive instance genericLanguageRule :: Generic LanguageRule _

instance encodeLanguageRule :: Encode LanguageRule where
  encode (LanguageRule r) = encode { regex: unsafeToForeign r.regex, action: r.action }

simpleRule :: Regex -> String -> LanguageRule
simpleRule regex token = LanguageRule { regex, action: Action { token, next: Nothing, log: Nothing } }

simpleRuleWithLog :: Regex -> String -> String -> LanguageRule
simpleRuleWithLog regex token msg = LanguageRule { regex, action: Action { token, next: Nothing, log: Just msg } }

simpleRuleWithAction :: Regex -> String -> String -> LanguageRule
simpleRuleWithAction regex token next = LanguageRule { regex, action: Action { token, next: Just next, log: Nothing } }

simpleRuleCases :: Regex -> Array (Tuple String String) -> LanguageRule
simpleRuleCases regex cases = LanguageRule { regex, action: Cases { log: Nothing, cases: (Object.fromFoldable cases) } }

simpleRuleCasesWithLog :: Regex -> String -> Array (Tuple String String) -> LanguageRule
simpleRuleCasesWithLog regex msg cases = LanguageRule { regex, action: Cases { log: Just msg, cases: (Object.fromFoldable cases) } }

foreign import data MonarchLanguage :: Type

foreign import data HoverProvider :: Type

foreign import data CompletionItemProvider :: Type

foreign import data CodeActionProvider :: Type

foreign import data IStandaloneThemeData :: Type

foreign import data DocumentFormattingEditProvider :: Type

foreign import data Monaco :: Type

foreign import data Editor :: Type

foreign import data ITextModel :: Type

foreign import data ITextMarker :: Type

foreign import data CompletionItemKind :: Type

foreign import completionItemKindEq_ :: Fn2 CompletionItemKind CompletionItemKind Boolean

instance eqCompletionItemKind :: Eq CompletionItemKind where
  eq = runFn2 completionItemKindEq_

foreign import completionItemKindOrd_ :: Fn5 Ordering Ordering Ordering CompletionItemKind CompletionItemKind Ordering

instance ordCompletionItemKind :: Ord CompletionItemKind where
  compare = runFn5 completionItemKindOrd_ LT EQ GT

foreign import data MarkerSeverity :: Type

instance encodeMarkerSeverity :: Encode MarkerSeverity where
  encode = encode <<< unsafeToForeign

instance decodeMarkerSeverity :: Decode MarkerSeverity where
  decode = pure <<< unsafeFromForeign

foreign import data TokensProvider :: Type

foreign import data Uri :: Type

instance encodeUri :: Encode Uri where
  encode = encode <<< unsafeToForeign

instance decodeUri :: Decode Uri where
  decode = pure <<< unsafeFromForeign

type IMarkdownString
  = { value :: String
    }

type IRange
  = { startLineNumber :: Int
    , startColumn :: Int
    , endLineNumber :: Int
    , endColumn :: Int
    }

type CompletionItem
  = { label :: String
    , kind :: CompletionItemKind
    , insertText :: String
    , range :: IRange
    , filterText :: String
    , sortText :: String
    , preselect :: Boolean
    }

type Marker r
  = ( severity :: MarkerSeverity
    , message :: String
    , startLineNumber :: Int
    , startColumn :: Int
    , endLineNumber :: Int
    , endColumn :: Int
    , code :: String
    , source :: String
    | r
    )

type IMarkerData
  = Record (Marker ())

getRange :: IMarkerData -> IRange
getRange { startLineNumber, startColumn, endLineNumber, endColumn } = { startLineNumber, startColumn, endLineNumber, endColumn }

type IMarker
  = Record (Marker ( owner :: String, resource :: Uri ))

type IPosition
  = { column :: Int
    , lineNumber :: Int
    }

type TextEdit
  = { range :: IRange
    , text :: String
    }

type WorkspaceTextEdit
  = { resource :: Uri
    , edit :: TextEdit
    }

type WorkspaceEdit
  = { edits :: Array WorkspaceTextEdit
    }

type CodeAction
  = { title :: String
    , edit :: WorkspaceEdit
    , kind :: String
    }

type Theme
  = { name :: String, themeData :: IStandaloneThemeData }

foreign import isWarning_ :: Fn1 MarkerSeverity Boolean

foreign import isError_ :: Fn1 MarkerSeverity Boolean

foreign import getMonaco :: Effect Monaco

foreign import create_ :: EffectFn3 Monaco HTMLElement String Editor

foreign import setTheme_ :: EffectFn2 Monaco String Unit

foreign import onDidChangeContent_ :: forall a. EffectFn2 Editor ({} -> Effect a) Unit

foreign import registerLanguage_ :: EffectFn2 Monaco Foreign Unit

foreign import defineTheme_ :: EffectFn2 Monaco Theme Unit

foreign import setMonarchTokensProvider_ :: EffectFn3 Monaco String MonarchLanguage Unit

foreign import setModelMarkers_ :: EffectFn4 Monaco ITextModel String (Array IMarkerData) Unit

foreign import getModelMarkers_ :: EffectFn2 Monaco ITextModel (Array IMarker)

foreign import addExtraTypesScriptLibsJS_ :: EffectFn1 Monaco Unit

foreign import setStrictNullChecks_ :: EffectFn2 Monaco Boolean Unit

foreign import setDeltaDecorations_ :: EffectFn3 Editor Int Int String

foreign import getModel_ :: EffectFn1 Editor ITextModel

foreign import getEditorId_ :: Fn1 Editor String

foreign import getValue_ :: Fn1 ITextModel String

foreign import setValue_ :: EffectFn2 ITextModel String Unit

foreign import getLineCount_ :: Fn1 ITextModel Int

foreign import setTokensProvider_ :: EffectFn3 Monaco String TokensProvider Unit

foreign import completionItemKind_ :: Fn1 String CompletionItemKind

foreign import markerSeverity_ :: Fn1 String MarkerSeverity

foreign import registerHoverProvider_ :: EffectFn3 Monaco String HoverProvider Unit

foreign import registerCompletionItemProvider_ :: EffectFn3 Monaco String CompletionItemProvider Unit

foreign import registerCodeActionProvider_ :: EffectFn3 Monaco String CodeActionProvider Unit

foreign import registerDocumentFormattingEditProvider_ :: EffectFn3 Monaco String DocumentFormattingEditProvider Unit

foreign import setPosition_ :: EffectFn2 Editor IPosition Unit

foreign import revealLine_ :: EffectFn2 Editor Int Unit

foreign import layout_ :: EffectFn1 Editor Unit

foreign import focus_ :: EffectFn1 Editor Unit

foreign import enableVimBindings_ :: EffectFn1 Editor (Effect Unit)

foreign import enableEmacsBindings_ :: EffectFn1 Editor (Effect Unit)

markerSeverity :: String -> MarkerSeverity
markerSeverity = runFn1 markerSeverity_

isWarning :: MarkerSeverity -> Boolean
isWarning = runFn1 isWarning_

isError :: MarkerSeverity -> Boolean
isError = runFn1 isError_

completionItemKind :: String -> CompletionItemKind
completionItemKind = runFn1 completionItemKind_

create :: Monaco -> HTMLElement -> String -> Effect Editor
create = runEffectFn3 create_

setTheme :: Monaco -> String -> Effect Unit
setTheme monaco themeName = runEffectFn2 setTheme_ monaco themeName

onDidChangeContent :: forall a. Editor -> ({} -> Effect a) -> Effect Unit
onDidChangeContent = runEffectFn2 onDidChangeContent_

registerLanguage :: Monaco -> LanguageExtensionPoint -> Effect Unit
registerLanguage monaco language =
  let
    languageF = encode language
  in
    runEffectFn2 registerLanguage_ monaco languageF

defineTheme :: Monaco -> Theme -> Effect Unit
defineTheme = runEffectFn2 defineTheme_

setMonarchTokensProvider :: Monaco -> String -> MonarchLanguage -> Effect Unit
setMonarchTokensProvider = runEffectFn3 setMonarchTokensProvider_

addExtraTypesScriptLibsJS :: Monaco -> Effect Unit
addExtraTypesScriptLibsJS = runEffectFn1 addExtraTypesScriptLibsJS_

setStrictNullChecks :: Monaco -> Boolean -> Effect Unit
setStrictNullChecks = runEffectFn2 setStrictNullChecks_

setDeltaDecorations :: Editor -> Int -> Int -> Effect String
setDeltaDecorations = runEffectFn3 setDeltaDecorations_

getModel :: Editor -> Effect ITextModel
getModel = runEffectFn1 getModel_

getEditorId :: Editor -> String
getEditorId = runFn1 getEditorId_

getValue :: ITextModel -> String
getValue = runFn1 getValue_

setValue :: ITextModel -> String -> Effect Unit
setValue = runEffectFn2 setValue_

getLineCount :: ITextModel -> Int
getLineCount = runFn1 getLineCount_

setModelMarkers :: Monaco -> ITextModel -> String -> Array IMarkerData -> Effect Unit
setModelMarkers = runEffectFn4 setModelMarkers_

getModelMarkers :: Monaco -> ITextModel -> Effect (Array IMarker)
getModelMarkers = runEffectFn2 getModelMarkers_

setTokensProvider :: Monaco -> String -> TokensProvider -> Effect Unit
setTokensProvider = runEffectFn3 setTokensProvider_

registerHoverProvider :: Monaco -> String -> HoverProvider -> Effect Unit
registerHoverProvider = runEffectFn3 registerHoverProvider_

registerCompletionItemProvider :: Monaco -> String -> CompletionItemProvider -> Effect Unit
registerCompletionItemProvider = runEffectFn3 registerCompletionItemProvider_

registerCodeActionProvider :: Monaco -> String -> CodeActionProvider -> Effect Unit
registerCodeActionProvider = runEffectFn3 registerCodeActionProvider_

registerDocumentFormattingEditProvider :: Monaco -> String -> DocumentFormattingEditProvider -> Effect Unit
registerDocumentFormattingEditProvider = runEffectFn3 registerDocumentFormattingEditProvider_

setPosition :: Editor -> IPosition -> Effect Unit
setPosition = runEffectFn2 setPosition_

revealLine :: Editor -> Int -> Effect Unit
revealLine = runEffectFn2 revealLine_

layout :: Editor -> Effect Unit
layout = runEffectFn1 layout_

focus :: Editor -> Effect Unit
focus = runEffectFn1 focus_

enableVimBindings :: Editor -> Effect (Effect Unit)
enableVimBindings = runEffectFn1 enableVimBindings_

enableEmacsBindings :: Editor -> Effect (Effect Unit)
enableEmacsBindings = runEffectFn1 enableEmacsBindings_
