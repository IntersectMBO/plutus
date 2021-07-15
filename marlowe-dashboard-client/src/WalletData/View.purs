module WalletData.View (walletDataCard) where

import Prelude hiding (div)
import Css as Css
import Data.Foldable (foldMap)
import Data.Lens (view, (^.))
import Data.Map (isEmpty, toUnfoldable)
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (unwrap)
import Data.String (null)
import Data.Tuple (Tuple(..))
import Data.UUID (toString) as UUID
import Halogen.Css (applyWhen, classNames, hideWhen)
import Halogen.HTML (HTML, button, div, h2, h3, input, label, li, p, p_, text, ul_)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (InputType(..), disabled, for, readOnly, type_, value)
import InputField.Lenses (_value)
import InputField.State (validate)
import InputField.Types (State) as InputField
import InputField.View (renderInput)
import Material.Icons (Icon(..)) as Icon
import WalletData.Lenses (_cardSection, _companionAppId, _walletIdInput, _walletNickname, _walletNicknameInput, _walletLibrary)
import WalletData.Types (Action(..), CardSection(..), State, WalletDetails, WalletIdError, WalletLibrary, WalletNicknameError)

walletDataCard :: forall p. State -> HTML p Action
walletDataCard state =
  let
    walletLibrary = state ^. _walletLibrary

    cardSection = state ^. _cardSection

    walletNicknameInput = state ^. _walletNicknameInput

    walletIdInput = state ^. _walletIdInput
  in
    case cardSection of
      Home -> walletLibraryCard walletLibrary
      ViewWallet walletDetails -> walletDetailsCard walletDetails
      NewWallet mTokenName -> newWalletCard walletNicknameInput walletIdInput mTokenName

walletLibraryCard :: forall p. WalletLibrary -> HTML p Action
walletLibraryCard library =
  div
    [ classNames [ "p-4" ] ]
    [ h2
        [ classNames [ "font-semibold", "text-lg", "mb-4" ] ]
        [ text "Contacts" ]
    , if isEmpty library then
        p_ [ text "You do not have any contacts." ]
      else
        ul_
          $ contactLi
          <$> toUnfoldable library
    , button
        [ classNames $ Css.primaryButton <> Css.withIcon Icon.NewContact <> Css.fixedBottomRight
        , onClick_ $ SetCardSection $ NewWallet Nothing
        ]
        [ text "New contact" ]
    ]
  where
  contactLi (Tuple nickname walletDetails) =
    li
      [ classNames [ "mt-4", "hover:cursor-pointer", "hover:text-green" ]
      , onClick_ $ SetCardSection $ ViewWallet walletDetails
      ]
      [ text nickname ]

walletDetailsCard :: forall p a. WalletDetails -> HTML p a
walletDetailsCard walletDetails =
  let
    walletNickname = view _walletNickname walletDetails

    companionAppId = view _companionAppId walletDetails
  in
    div [ classNames [ "p-5", "pb-6", "md:pb-8" ] ]
      [ h3
          [ classNames [ "font-semibold", "mb-4" ] ]
          [ text $ "Wallet " <> walletNickname ]
      , div
          [ classNames Css.hasNestedLabel ]
          [ label
              [ classNames Css.nestedLabel ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ Css.input true <> [ "mb-4" ]
              , value $ UUID.toString $ unwrap companionAppId
              , readOnly true
              ]
          ]
      ]

newWalletCard :: forall p. InputField.State WalletNicknameError -> InputField.State WalletIdError -> Maybe String -> HTML p Action
newWalletCard walletNicknameInput walletIdInput mTokenName =
  let
    walletNickname = view _value walletNicknameInput

    walletIdString = view _value walletIdInput

    walletNicknameInputDisplayOptions =
      { additionalCss: mempty
      , id_: "newWalletNickname"
      , placeholder: "Nickname"
      , readOnly: false
      , numberFormat: Nothing
      , valueOptions: mempty
      }

    walletIdInputDisplayOptions =
      { additionalCss: mempty
      , id_: "newWalletId"
      , placeholder: "Wallet ID"
      , readOnly: false
      , numberFormat: Nothing
      , valueOptions: mempty
      }
  in
    div
      [ classNames [ "flex", "flex-col", "p-5", "pb-6", "md:pb-8" ] ]
      [ p
          [ classNames [ "font-semibold", "mb-4" ] ]
          [ text $ "Create new contact" <> foldMap (\tokenName -> " for role " <> show tokenName) mTokenName ]
      , div
          [ classNames $ [ "mb-4" ] <> (applyWhen (not null walletNickname) Css.hasNestedLabel) ]
          [ label
              [ classNames $ Css.nestedLabel <> hideWhen (null walletNickname)
              , for walletNicknameInputDisplayOptions.id_
              ]
              [ text "Nickname" ]
          , WalletNicknameInputAction <$> renderInput walletNicknameInputDisplayOptions walletNicknameInput
          ]
      , div
          [ classNames $ [ "mb-4" ] <> (applyWhen (not null walletIdString) Css.hasNestedLabel) ]
          [ label
              [ classNames $ Css.nestedLabel <> hideWhen (null walletIdString)
              , for walletIdInputDisplayOptions.id_
              ]
              [ text "Wallet ID" ]
          , WalletIdInputAction <$> renderInput walletIdInputDisplayOptions walletIdInput
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
              , onClick_ CloseWalletDataCard
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , disabled $ isJust (validate walletNicknameInput) || isJust (validate walletIdInput)
              , onClick_ $ SaveWallet mTokenName
              ]
              [ text "Save" ]
          ]
      ]
