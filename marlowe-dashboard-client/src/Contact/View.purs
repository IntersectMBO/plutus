module Contact.View
  ( renderContacts
  , renderNewContact
  , renderContact
  ) where

import Prelude hiding (div)
import Contact.Lenses (_key, _nickname)
import Contact.Types (Action(..), Contact)
import Contact.Validation (keyError, nicknameError)
import Css (buttonClasses, classNames, h2Classes, textInputClasses, toggleWhen)
import Data.Array (head, sort)
import Data.Lens (view)
import Data.Maybe (Maybe(..))
import Halogen.HTML (HTML, button, div, h2, input, li, p_, span, text, ul)
import Halogen.HTML.Events (onClick, onValueInput)
import Halogen.HTML.Properties (InputType(..), disabled, placeholder, type_, value)
import Material.Icons as Icon

renderContacts :: forall p. Array Contact -> HTML p Action
renderContacts contacts =
  div
    [ classNames [ "p-1" ] ]
    [ div
        [ classNames [ "flex", "justify-between" ] ]
        [ h2
            [ classNames h2Classes ]
            [ text "Contacts" ]
        , button
            [ classNames $ buttonClasses <> [ "flex", "items-center", "text-green" ]
            , onClick $ const $ Just $ ToggleNewContactCard
            ]
            [ span
                [ classNames [ "mr-0.5" ] ]
                [ text "Create New" ]
            , Icon.addCircle
            ]
        ]
    , case head contacts of
        Nothing -> p_ [ text "You do not have any contacts." ]
        _ ->
          ul
            [ classNames [ "mt-1", "border-t", "border-blue" ] ]
            $ contactLi
            <$> sort contacts
    ]
  where
  contactLi contact =
    li
      [ classNames [ "mt-1", "hover:cursor-pointer", "hover:text-green" ]
      , onClick $ const $ Just $ ToggleEditContactCard contact
      ]
      [ text $ view _nickname contact ]

renderNewContact :: forall p. Array Contact -> Contact -> HTML p Action
renderNewContact contacts newContact =
  let
    key = view _key newContact

    nickname = view _nickname newContact

    mKeyError = keyError key contacts

    mNicknameError = nicknameError nickname contacts
  in
    div
      [ classNames [ "flex", "flex-col" ] ]
      [ h2
          [ classNames h2Classes ]
          [ text "New Contact" ]
      , input
          [ type_ InputText
          , classNames $ textInputClasses <> toggleWhen (mKeyError == Nothing) "border-green" "border-red"
          , placeholder "Wallet key"
          , value key
          , onValueInput $ Just <<< SetNewContactKey
          ]
      , div
          [ classNames [ "mb-1", "text-red", "text-sm" ] ]
          $ case mKeyError of
              Just keyError -> [ text $ show keyError ]
              Nothing -> []
      , input
          [ type_ InputText
          , classNames $ textInputClasses <> toggleWhen (mNicknameError == Nothing) "border-green" "border-red"
          , placeholder "Nickname"
          , value nickname
          , onValueInput $ Just <<< SetNewContactNickname
          ]
      , div
          [ classNames [ "mb-1", "text-red", "text-sm" ] ]
          $ case mNicknameError of
              Just nicknameError -> [ text $ show nicknameError ]
              Nothing -> []
      , button
          [ classNames $ buttonClasses <> [ "bg-green", "text-white" ]
          , disabled $ not $ mKeyError == Nothing && mNicknameError == Nothing
          , onClick $ const $ Just AddNewContact
          ]
          [ text "Save contact" ]
      ]

renderContact :: forall p. Contact -> HTML p Action
renderContact contact =
  div
    [ classNames [ "flex", "flex-col" ] ]
    [ h2
        [ classNames h2Classes ]
        [ text "Contact Details" ]
    , p_ [ text $ "Key: " <> view _key contact ]
    , p_ [ text $ "Nickname: " <> view _nickname contact ]
    ]
