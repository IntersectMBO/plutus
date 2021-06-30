module WalletData.View
  ( saveWalletCard
  , walletDetailsCard
  , putdownWalletCard
  , walletLibraryScreen
  ) where

import Prelude hiding (div)
import Css as Css
import Dashboard.Types (Action(..), Card(..))
import Data.Foldable (foldMap)
import Data.Lens (view)
import Data.Map (isEmpty, toUnfoldable)
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (unwrap)
import Data.String (null)
import Data.Tuple (Tuple(..))
import Data.UUID (toString) as UUID
import Halogen.Css (applyWhen, classNames, hideWhen)
import Halogen.HTML (HTML, button, div, h2, h3, h4, input, label, li, p, p_, text, ul_)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (InputType(..), disabled, for, readOnly, type_, value)
import Humanize (humanizeValue)
import InputField.Lenses (_value)
import InputField.State (validate)
import InputField.Types (State) as InputField
import InputField.View (renderInput)
import Material.Icons (Icon(..))
import Types (WebData)
import WalletData.Lenses (_assets, _companionAppId, _walletNickname)
import WalletData.State (adaToken, getAda)
import WalletData.Types (WalletDetails, WalletInfo, WalletLibrary)
import WalletData.Validation (WalletIdError, WalletNicknameError)

saveWalletCard :: forall p. WalletLibrary -> InputField.State WalletNicknameError -> InputField.State WalletIdError -> WebData WalletInfo -> Maybe String -> HTML p Action
saveWalletCard walletLibrary walletNicknameInput walletIdInput remoteWalletInfo mTokenName =
  let
    walletNickname = view _value walletNicknameInput

    walletIdString = view _value walletIdInput

    walletNicknameInputDisplayOptions =
      { baseCss: Css.input
      , additionalCss: mempty
      , id_: "newWalletNickname"
      , placeholder: "Nickname"
      , readOnly: false
      , valueOptions: mempty
      }

    walletIdInputDisplayOptions =
      { baseCss: Css.input
      , additionalCss: mempty
      , id_: "newWalletId"
      , placeholder: "Wallet ID"
      , readOnly: false
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
          , WalletNicknameInputAction <$> renderInput walletNicknameInput walletNicknameInputDisplayOptions
          ]
      , div
          [ classNames $ [ "mb-4" ] <> (applyWhen (not null walletIdString) Css.hasNestedLabel) ]
          [ label
              [ classNames $ Css.nestedLabel <> hideWhen (null walletIdString)
              , for walletIdInputDisplayOptions.id_
              ]
              [ text "Wallet ID" ]
          , WalletIdInputAction <$> renderInput walletIdInput walletIdInputDisplayOptions
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
              , onClick_ $ CloseCard $ SaveWalletCard Nothing
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , disabled $ isJust (validate walletNicknameInput) || isJust (validate walletIdInput)
              , onClick_ $ SaveNewWallet mTokenName
              ]
              [ text "Save" ]
          ]
      ]

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
              , classNames $ Css.input false <> [ "mb-4" ]
              , value $ UUID.toString $ unwrap companionAppId
              , readOnly true
              ]
          ]
      ]

putdownWalletCard :: forall p. WalletDetails -> HTML p Action
putdownWalletCard walletDetails =
  let
    walletNickname = view _walletNickname walletDetails

    companionAppId = view _companionAppId walletDetails

    assets = view _assets walletDetails
  in
    div [ classNames [ "p-5", "pb-6", "md:pb-8" ] ]
      [ h3
          [ classNames [ "font-semibold", "mb-4", "truncate", "w-11/12" ] ]
          [ text $ "Wallet " <> walletNickname ]
      , div
          [ classNames Css.hasNestedLabel ]
          [ label
              [ classNames Css.nestedLabel ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ Css.input false <> [ "mb-4" ]
              , value $ UUID.toString $ unwrap companionAppId
              , readOnly true
              ]
          ]
      , div
          [ classNames [ "mb-4" ] ]
          [ h4
              [ classNames [ "font-semibold" ] ]
              [ text "Balance:" ]
          , p
              [ classNames Css.funds ]
              [ text $ humanizeValue adaToken $ getAda assets ]
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
              , onClick_ $ CloseCard PutdownWalletCard
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , onClick_ PutdownWallet
              ]
              [ text "Drop wallet" ]
          ]
      ]

walletLibraryScreen :: forall p. WalletLibrary -> HTML p Action
walletLibraryScreen library =
  div
    [ classNames [ "p-4", "md:px-5pc" ] ]
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
        [ classNames $ Css.primaryButton <> Css.withIcon NewContact <> Css.fixedBottomRight
        , onClick_ $ OpenCard $ SaveWalletCard Nothing
        ]
        [ text "New contact" ]
    ]
  where
  contactLi (Tuple nickname walletDetails) =
    li
      [ classNames [ "mt-4", "hover:cursor-pointer", "hover:text-green" ]
      , onClick_ $ OpenCard $ ViewWalletCard walletDetails
      ]
      [ text nickname ]
