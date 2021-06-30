module Toast.View (renderToast) where

import Prelude hiding (div)
import Css as Css
import Data.Lens (preview)
import Data.Maybe (Maybe(..), fromMaybe)
import Halogen (RefLabel(..))
import Halogen.Css (classNames)
import Halogen.HTML (HTML, a, div, div_, span, span_, text)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (ref)
import Material.Icons (Icon(..), icon_, icon)
import Toast.Lenses (_expanded, _toastMessage)
import Toast.Types (Action(..), State, ToastMessage)

renderToast ::
  forall p.
  State ->
  HTML p Action
renderToast state = doRender (preview _toastMessage state) (fromMaybe false $ preview _expanded state)
  where
  doRender Nothing _ = div_ []

  doRender (Just toast) true = renderExpanded toast

  doRender (Just toast) false = renderCollapsed toast

renderExpanded ::
  forall p.
  ToastMessage ->
  HTML p Action
renderExpanded toast =
  div
    [ classNames $ Css.overlay false ]
    [ div
        [ classNames $ Css.card false ]
        [ a
            [ classNames [ "absolute", "top-4", "right-4", toast.textColor ]
            , onClick_ CloseToast
            ]
            [ icon_ Close ]
        , div [ classNames [ "flex", "font-semibold", "px-5", "py-4", toast.bgColor, toast.textColor ] ]
            [ icon toast.icon [ "mr-2", toast.iconColor ]
            , span_ [ text toast.shortDescription ]
            ]
        , div [ classNames [ "px-5", "pb-6", "pt-3", "md:pb-8" ] ]
            [ text $ fromMaybe "" toast.longDescription
            ]
        ]
    ]

renderCollapsed ::
  forall p.
  ToastMessage ->
  HTML p Action
renderCollapsed toast =
  let
    readMore = case toast.longDescription of
      Nothing -> div_ []
      Just _ ->
        div [ classNames [ "ml-4", "font-semibold", "underline", "flex-shrink-0" ] ]
          [ a
              [ onClick_ ExpandToast
              ]
              [ text "Read more" ]
          ]
  in
    div
      [ classNames [ "fixed", "bottom-6", "md:bottom-10", "left-0", "right-0", "flex", "justify-center", "z-50" ] ]
      [ div
          [ classNames [ "px-4", "py-2", "rounded", "shadow-lg", "min-w-90p", "max-w-90p", "sm:min-w-sm", "flex", "justify-between", "animate-from-below", toast.bgColor, toast.textColor ]
          , ref
              (RefLabel "collapsed-toast")
          ]
          [ div [ classNames [ "flex", "overflow-hidden" ] ]
              [ icon toast.icon [ "mr-2", toast.iconColor ]
              , span [ classNames [ "font-semibold", "overflow-ellipsis", "whitespace-nowrap", "overflow-hidden" ] ] [ text toast.shortDescription ]
              ]
          , readMore
          ]
      ]
