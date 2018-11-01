module MainFrame
  ( mainFrame
  ) where

import Debug.Trace

import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceEffects, AceMessage(..), AceQuery, aceComponent)
import Ace.Types (ACE, Editor)
import Action (actionsPane)
import Bootstrap (col, col9, container, row)
import Control.Monad.Aff (Aff)
import Control.Monad.Eff.Class (liftEff)
import Data.Array as Array
import Data.Either.Nested (Either2)
import Data.Functor.Coproduct.Nested (Coproduct2)
import Data.Lens (modifying)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple.Nested ((/\))
import ECharts.Commands as E
import ECharts.Monad (CommandsT, interpret)
import ECharts.Types.Phantom (I)
import Halogen (Component)
import Halogen as H
import Halogen.Component (ParentHTML)
import Halogen.Component.ChildPath (ChildPath, cp1, cp2)
import Halogen.ECharts (EChartsEffects, EChartsQuery, echarts)
import Halogen.ECharts as EC
import Halogen.HTML (ClassName(ClassName), HTML, a, div, div_, h1_, h2_, h3_, hr_, p_, slot', text)
import Halogen.HTML.Events (input)
import Halogen.HTML.Properties (class_, href, target)
import Halogen.Query (HalogenM)
import Prelude (class Eq, class Monad, class Ord, type (~>), Unit, Void, bind, const, discard, flip, pure, unit, void, ($), (<*>))
import StaticData (staticWallets)
import Types (Query(HandleEChartsMessage, HandleAceMessage, KillAction, SendAction), State, _actions, State)
import Wallet (walletsPane)

initialState :: State
initialState =
  { actions: []
  , wallets: staticWallets
  }

initialText :: String
initialText = """{-# LANGUAGE TemplatePlutus #-}


module Main where

main :: IO ()
main = do
  putStrLn "Hello"
  putStrLn "Plutus"
"""
------------------------------------------------------------

type ChildQuery = Coproduct2 AceQuery EChartsQuery
type ChildSlot = Either2 AceSlot EChartsSlot

data AceSlot = AceSlot
derive instance eqComponentAceSlot :: Eq AceSlot
derive instance ordComponentAceSlot :: Ord AceSlot

data EChartsSlot = EChartsSlot
derive instance eqComponentEChartsSlot :: Eq EChartsSlot
derive instance ordComponentEChartsSlot :: Ord EChartsSlot

cpAce :: ChildPath AceQuery ChildQuery AceSlot ChildSlot
cpAce = cp1

cpECharts :: ChildPath EChartsQuery ChildQuery EChartsSlot ChildSlot
cpECharts = cp2

------------------------------------------------------------

mainFrame :: forall aff. Component HTML Query Unit Void (Aff (EChartsEffects (AceEffects aff)))
mainFrame =
  H.parentComponent
    { initialState: const initialState
    , render
    , eval
    , receiver: const Nothing
    }

eval :: forall m. Query ~> HalogenM State Query ChildQuery ChildSlot Void m
eval (HandleAceMessage (TextChanged msg) next) = do
  void $ traceAnyM msg
  pure next

eval (HandleEChartsMessage EC.Initialized next) = do
  void $ H.query' cp2 EChartsSlot $ H.action $ EC.Set $ interpret sankeyDiagramOptions
  pure next

-- We just ignore most ECharts events.
eval (HandleEChartsMessage (EC.EventRaised event) next) =
  pure next

eval (SendAction action next) = do
  modifying _actions $ flip Array.snoc action
  pure next

eval (KillAction index next) = do
  modifying _actions $ (fromMaybe <*> Array.deleteAt index)
  pure next

------------------------------------------------------------

initEditor ∷ forall aff. Editor -> Aff (ace :: ACE | aff) Unit
initEditor editor = liftEff $ do
  session <- Editor.getSession editor
  Session.setMode "ace/mode/haskell" session
  void $ Editor.setValue initialText (Just 1) editor

render :: forall aff. State -> ParentHTML Query ChildQuery ChildSlot (Aff (EChartsEffects (AceEffects aff)))
render state =
  div [ class_ (ClassName "main-frame") ] $
    [ container
      [ header
      , hr_
      , editorPane
      , hr_
      , mockChainPane state
      ]
    ]

header :: forall p i. HTML p i
header =
  row
    [ col [ h1_ [ text "Plutus Playground" ] ]
    , col
      [ p_ [
          a [ href "https://github.com/input-output-hk/plutus/tree/mchakravarty/plutus-playground-spec/docs/playground"
            , target "_blank"
            ]
            [ text "Design Document" ]
          ]
      ]
    ]

editorPane :: forall aff. ParentHTML Query ChildQuery ChildSlot (Aff (EChartsEffects (AceEffects aff)))
editorPane =
  div_
    [ slot' cpAce AceSlot
        (aceComponent initEditor Nothing)
        unit
        (input HandleAceMessage)
    ]

mockChainPane :: forall aff. State -> ParentHTML Query ChildQuery ChildSlot (Aff (EChartsEffects (AceEffects aff)))
mockChainPane state =
  div_
    [ row
        [ col9 [ walletsPane state.wallets ]
        , col [ actionsPane state.actions  ]
        ]
    , h3_ [ text "Chain" ]
    , slot' cpECharts EChartsSlot
        (echarts Nothing)
        ({width: 800, height: 800} /\ unit)
        (input HandleEChartsMessage)
    ]

sankeyDiagramOptions :: forall m i. Monad m => CommandsT (series :: I | i) m Unit
sankeyDiagramOptions = do
  E.series $ E.sankey do
    E.buildItems do
      E.addItem do
        E.name "charles"
        E.value 600.0
      E.addItem do
        E.name "kris"
        E.value 10.0
      E.addItem do
        E.name "david"
        E.value 15.0
      E.addItem do
        E.name "manuel"
        E.value 123.0
    E.buildLinks do
      E.addLink do
        E.sourceName "charles"
        E.targetName "kris"
        E.value 10.0
      E.addLink do
        E.sourceName "charles"
        E.targetName "david"
        E.value 10.0
      E.addLink do
        E.sourceName "charles"
        E.targetName "manuel"
        E.value 20.0

      E.addLink do
        E.sourceName "manuel"
        E.targetName "kris"
        E.value 5.0
      E.addLink do
        E.sourceName "manuel"
        E.targetName "david"
        E.value 5.0
