module WalletData.View
  ( saveWalletCard
  , walletDetailsCard
  , putdownWalletCard
  , walletLibraryScreen
  , nicknamesDataList
  ) where

import Prelude hiding (div)
import Css (applyWhen, classNames, hideWhen)
import Css as Css
import Data.Foldable (foldMap)
import Data.Lens (view)
import Data.Map (isEmpty, toUnfoldable)
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (unwrap)
import Data.String (null)
import Data.Tuple (Tuple(..))
import Data.UUID (toString) as UUID
import Halogen.HTML (HTML, button, datalist, div, h2, h3, h4, input, label, li, option, p, p_, text, ul_)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), disabled, id_, placeholder, readOnly, type_, value)
import Humanize (humanizeValue)
import Material.Icons (Icon(..))
import Play.Types (Action(..), Card(..))
import Types (WebData)
import WalletData.Lenses (_assets, _companionContractId, _walletNickname)
import WalletData.State (adaToken, getAda)
import WalletData.Types (WalletDetails, WalletInfo, WalletLibrary, WalletNickname)
import WalletData.Validation (contractInstanceIdError, walletNicknameError)

saveWalletCard :: forall p. WalletLibrary -> WalletNickname -> String -> WebData WalletInfo -> Maybe String -> HTML p Action
saveWalletCard walletLibrary newWalletNickname newWalletContractIdString newWalletInfo mTokenName =
  let
    mWalletNicknameError = walletNicknameError newWalletNickname walletLibrary

    mContractInstanceIdError = contractInstanceIdError newWalletContractIdString newWalletInfo walletLibrary
  in
    div
      [ classNames [ "flex", "flex-col", "p-5", "pb-6", "md:pb-8" ] ]
      [ p
          [ classNames [ "font-semibold", "mb-4" ] ]
          [ text $ "Create new contact" <> foldMap (\tokenName -> " for role " <> show tokenName) mTokenName ]
      , div
          [ classNames $ [ "mb-4" ] <> (applyWhen (not null newWalletNickname) Css.hasNestedLabel) ]
          [ label
              [ classNames $ Css.nestedLabel <> hideWhen (null newWalletNickname) ]
              [ text "Nickname" ]
          , input
              [ type_ InputText
              , classNames $ Css.input $ isJust mWalletNicknameError
              , placeholder "Nickname"
              , value newWalletNickname
              , onValueInput_ SetNewWalletNickname
              ]
          , div
              [ classNames Css.inputError ]
              [ text $ foldMap show mWalletNicknameError ]
          ]
      , div
          [ classNames $ [ "mb-4" ] <> (applyWhen (not null newWalletContractIdString) Css.hasNestedLabel) ]
          [ label
              [ classNames $ Css.nestedLabel <> hideWhen (null newWalletContractIdString) ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ Css.input $ isJust mContractInstanceIdError
              , placeholder "Wallet ID"
              , value newWalletContractIdString
              , onValueInput_ SetNewWalletContractIdString
              ]
          , div
              [ classNames Css.inputError ]
              [ text $ foldMap show mContractInstanceIdError ]
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
              , onClick_ CloseCard
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , disabled $ isJust mWalletNicknameError || isJust mContractInstanceIdError
              , onClick_ $ SaveNewWallet mTokenName
              ]
              [ text "Save" ]
          ]
      ]

walletDetailsCard :: forall p a. WalletDetails -> HTML p a
walletDetailsCard walletDetails =
  let
    walletNickname = view _walletNickname walletDetails

    contractInstanceId = view _companionContractId walletDetails
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
              , value $ UUID.toString $ unwrap contractInstanceId
              , readOnly true
              ]
          ]
      ]

putdownWalletCard :: forall p. WalletDetails -> HTML p Action
putdownWalletCard walletDetails =
  let
    walletNickname = view _walletNickname walletDetails

    contractInstanceId = view _companionContractId walletDetails

    assets = view _assets walletDetails
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
              , value $ UUID.toString $ unwrap contractInstanceId
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
              , onClick_ CloseCard
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
        [ classNames $ Css.primaryButton <> Css.withIcon Add <> Css.fixedBottomRight
        , onClick_ $ OpenCard $ SaveWalletCard Nothing
        ]
        [ text "New contact" ]
    ]
  where
  contactLi (Tuple nickname walletDetails) =
    let
      contractId = view _companionContractId walletDetails
    in
      li
        [ classNames [ "mt-4", "hover:cursor-pointer", "hover:text-green" ]
        , onClick_ $ OpenCard $ ViewWalletCard walletDetails
        ]
        [ text nickname ]

nicknamesDataList :: forall p a. WalletLibrary -> HTML p a
nicknamesDataList library =
  datalist
    [ id_ "walletNicknames" ]
    $ walletOption
    <$> toUnfoldable library
  where
  walletOption (Tuple nickname _) = option [ value nickname ] []
