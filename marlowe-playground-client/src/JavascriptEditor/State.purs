module JavascriptEditor.State where

import Prelude hiding (div)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (_Just, assign, to, use, view)
import Data.Lens.Extra (peruse)
import Data.List ((:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (drop, joinWith, length, take)
import Effect.Aff.Class (class MonadAff, liftAff)
import Halogen (HalogenM, liftEffect, query)
import Halogen.Blockly as Blockly
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import JavascriptEditor.Types (Action(..), CompilationState(..), State, _compilationResult, _decorationIds, _keybindings, _showBottomPanel)
import Language.Javascript.Interpreter (_result)
import Language.Javascript.Interpreter as JSI
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _blocklySlot, _jsEditorSlot)
import Marlowe (SPParams_)
import Monaco (IRange, isError)
import Servant.PureScript.Settings (SPSettings_)
import StaticData (jsBufferLocalStorageKey)
import StaticData as StaticData
import Text.Parsing.StringParser.Basic (lines)

checkDecorationPosition :: Int -> Maybe IRange -> Maybe IRange -> Boolean
checkDecorationPosition numLines (Just { endLineNumber }) (Just { startLineNumber }) = (endLineNumber == headerLength) && (startLineNumber == numLines - footerLength + 1)
  where
  headerLength = Array.length decorationHeader

  footerLength = Array.length decorationFooter

checkDecorationPosition _ _ _ = false

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction _ (HandleEditorMessage (Monaco.TextChanged text)) =
  ( do
      let
        prunedText = pruneJSboilerplate text

        numLines = Array.length $ lines text
      mDecorIds <- peruse (_decorationIds <<< _Just)
      case mDecorIds of
        Just decorIds -> do
          mRangeHeader <- query _jsEditorSlot unit (Monaco.GetDecorationRange decorIds.topDecorationId identity)
          mRangeFooter <- query _jsEditorSlot unit (Monaco.GetDecorationRange decorIds.bottomDecorationId identity)
          mContent <- liftEffect $ LocalStorage.getItem jsBufferLocalStorageKey
          if (mContent == Just text) || (checkJSboilerplate text && checkDecorationPosition numLines mRangeHeader mRangeFooter) then
            ( do
                liftEffect $ LocalStorage.setItem jsBufferLocalStorageKey prunedText
                assign _compilationResult NotCompiled
            )
          else
            editorSetValue (fromMaybe "" mContent)
        Nothing -> editorSetValue prunedText
  )

handleAction _ (ChangeKeyBindings bindings) = do
  assign _keybindings bindings
  void $ query _jsEditorSlot unit (Monaco.SetKeyBindings bindings unit)

handleAction settings Compile = do
  maybeModel <- query _jsEditorSlot unit (Monaco.GetModel identity)
  compilationResult <- case maybeModel of
    Nothing -> pure NotCompiled
    Just model -> do
      assign _compilationResult Compiling
      maybeMarkers <- query _jsEditorSlot unit (Monaco.GetModelMarkers identity)
      case map ((List.filter (\e -> isError e.severity)) <<< Array.toUnfoldable) maybeMarkers of
        Just ({ message, startLineNumber, startColumn } : _) ->
          pure $ CompilationError
            $ JSI.CompilationError
                { row: startLineNumber
                , column: startColumn
                , text: [ message ]
                }
        _ -> do
          res <- liftAff $ JSI.eval model
          case res of
            Left err -> pure $ CompilationError err
            Right result -> pure $ CompiledSuccessfully result
  assign _compilationResult compilationResult
  assign _showBottomPanel true
  editorResize

handleAction _ (LoadScript key) = do
  case Map.lookup key StaticData.demoFilesJS of
    Nothing -> pure unit
    Just contents -> do
      editorSetValue contents

handleAction _ (ShowBottomPanel val) = do
  assign _showBottomPanel val
  editorResize

handleAction _ SendResultToSimulator = pure unit

handleAction _ SendResultToBlockly = do
  mContract <- use _compilationResult
  case mContract of
    CompiledSuccessfully result -> do
      let
        source = view (_result <<< to show) result
      void $ query _blocklySlot unit (Blockly.SetCode source unit)
    _ -> pure unit

editorResize :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorResize = void $ query _jsEditorSlot unit (Monaco.Resize unit)

decorationHeader :: Array String
decorationHeader =
  [ "import {"
  , "    PK, Role, Account, Party, ada, AvailableMoney, Constant, NegValue, AddValue,"
  , "    SubValue, MulValue, Scale, ChoiceValue, SlotIntervalStart, SlotIntervalEnd,"
  , "    UseValue, Cond, AndObs, OrObs, NotObs, ChoseSomething, ValueGE, ValueGT,"
  , "    ValueLT, ValueLE, ValueEQ, TrueObs, FalseObs, Deposit, Choice, Notify,"
  , "    Close, Pay, If, When, Let, Assert, SomeNumber, AccountId, ChoiceId, Token,"
  , "    ValueId, Value, EValue, Observation, Bound, Action, Payee, Case, Contract"
  , "} from 'marlowe-js';"
  , ""
  , "(function (): Contract {"
  ]

decorationFooter :: Array String
decorationFooter = [ "})" ]

decorationHeaderString :: String
decorationHeaderString = joinWith "\n" decorationHeader

lengthOfHeader :: Int
lengthOfHeader = length decorationHeaderString

decorationFooterString :: String
decorationFooterString = joinWith "\n" decorationFooter

lengthOfFooter :: Int
lengthOfFooter = length decorationFooterString

editorSetValue ::
  forall m.
  MonadAff m =>
  String ->
  HalogenM State Action ChildSlots Void m Unit
editorSetValue contents = do
  let
    decoratedContent = joinWith "\n" [ decorationHeaderString, contents, decorationFooterString ]

    numLines = Array.length $ lines decoratedContent
  void $ query _jsEditorSlot unit $ Monaco.SetText decoratedContent unit
  mTopDecorationId <- query _jsEditorSlot unit $ Monaco.SetDeltaDecorations 1 (Array.length decorationHeader) identity
  mBottomDecorationId <- query _jsEditorSlot unit $ Monaco.SetDeltaDecorations (numLines - Array.length decorationFooter + 1) numLines identity
  for_ mTopDecorationId
    ( \topDecorationId ->
        for_ mBottomDecorationId
          ( \bottomDecorationId ->
              assign _decorationIds
                ( Just
                    { topDecorationId: topDecorationId
                    , bottomDecorationId: bottomDecorationId
                    }
                )
          )
    )

checkJSboilerplate :: String -> Boolean
checkJSboilerplate content =
  let
    header = (take (lengthOfHeader + 1) content)

    footer = (drop (length content - lengthOfFooter - 1) content)
  in
    (header == decorationHeaderString <> "\n") && (footer == "\n" <> decorationFooterString)

pruneJSboilerplate :: String -> String
pruneJSboilerplate content =
  let
    noHeader = (drop (lengthOfHeader + 1) content)
  in
    take (length noHeader - lengthOfFooter - 1) noHeader

editorGetValue ::
  forall m.
  MonadAff m =>
  HalogenM State Action ChildSlots Void m (Maybe String)
editorGetValue = do
  mContent <- query _jsEditorSlot unit (Monaco.GetText identity)
  pure
    ( map
        pruneJSboilerplate
        mContent
    )
