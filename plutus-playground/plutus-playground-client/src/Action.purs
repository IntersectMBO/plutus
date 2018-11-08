module Action where

import Bootstrap (bgInfo, btn, btnInfo, btnPrimary, btnSmall, card, cardBody_, pullRight, textWhite)
import Data.Array (mapWithIndex)
import Data.Foldable (intercalate)
import Data.Newtype (unwrap)
import Halogen (HTML)
import Halogen.HTML (ClassName(ClassName), br_, button, div, div_, h3_, text)
import Halogen.HTML.Events (input_, onClick)
import Halogen.HTML.Properties (class_, classes)
import Icons (Icon(..), icon)
import Prelude (pure, ($), (<<<))
import Types (Action, Query(..))
import Wallet (walletIdPane)

actionsPane :: forall p. Array Action -> HTML p Query
actionsPane actions =
  div [ class_ $ ClassName "actions" ]
    [ h3_ [ text "Actions" ]
    , div_
      (
        intercalate
          [ icon LongArrowDown ]
          (mapWithIndex (\index -> pure <<< actionPane index) actions)
      )
    , br_
    , evaluateActionsPane
    ]

actionPane :: forall p. Int -> Action -> HTML p Query
actionPane index action =
  div [ class_ $ ClassName "action" ]
    [ div [ classes [ card, textWhite, bgInfo ] ]
      [ cardBody_
        [ button
            [ classes [ btn, btnInfo, pullRight ]
            , onClick $ input_ $ KillAction index
            ]
            [ icon Close ]
        , div_ [ walletIdPane action.walletId ]
        , div_ [ text (unwrap action.actionId) ]
        ]
      ]
    ]

evaluateActionsPane :: forall p. HTML p Query
evaluateActionsPane =
  button
    [ classes [ btn, btnPrimary, btnSmall ]
    , onClick $ input_ EvaluateActions
    ]
    [ text "Evaluate" ]
