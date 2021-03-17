module WalletData.View
  ( newWalletCard
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
import Data.String (null)
import Data.Tuple (Tuple(..))
import Halogen.HTML (HTML, button, datalist, div, div_, h2, h3, input, label, li, option, p, p_, text, ul_)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), disabled, id_, placeholder, readOnly, type_, value)
import Marlowe.Semantics (PubKey)
import Material.Icons (Icon(..))
import Network.RemoteData (RemoteData)
import Play.Types (Action(..), Card(..))
import Servant.PureScript.Ajax (AjaxError)
import WalletData.Lenses (_contractId, _nickname)
import WalletData.Types (Nickname, WalletDetails, WalletLibrary)
import WalletData.Validation (contractIdError, nicknameError)

newWalletCard :: forall p. WalletLibrary -> Nickname -> String -> RemoteData AjaxError PubKey -> Maybe String -> HTML p Action
newWalletCard library newWalletNickname newWalletContractId remoteDataPubKey mTokenName =
  let
    mNicknameError = nicknameError newWalletNickname library

    mContractIdError = contractIdError newWalletContractId remoteDataPubKey library
  in
    div
      [ classNames [ "flex", "flex-col" ] ]
      [ p
          [ classNames [ "mb-4" ] ]
          [ text $ "Create new contact" <> foldMap (\tokenName -> " for role " <> show tokenName) mTokenName ]
      , div
          [ classNames $ [ "mb-4" ] <> (applyWhen (not null newWalletNickname) Css.hasNestedLabel) ]
          [ label
              [ classNames $ Css.nestedLabel <> hideWhen (null newWalletNickname) ]
              [ text "Nickname" ]
          , input
              [ type_ InputText
              , classNames $ Css.input $ isJust mNicknameError
              , placeholder "Nickname"
              , value newWalletNickname
              , onValueInput_ SetNewWalletNickname
              ]
          , div
              [ classNames Css.inputError ]
              [ text $ foldMap show mNicknameError ]
          ]
      , div
          [ classNames $ [ "mb-4" ] <> (applyWhen (not null newWalletContractId) Css.hasNestedLabel) ]
          [ label
              [ classNames $ Css.nestedLabel <> hideWhen (null newWalletContractId) ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ Css.input $ isJust mContractIdError
              , placeholder "Wallet ID"
              , value newWalletContractId
              , onValueInput_ SetNewWalletContractId
              ]
          , div
              [ classNames Css.inputError ]
              [ text $ foldMap show mContractIdError ]
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
              , onClick_ $ SetCard Nothing
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , disabled $ isJust mNicknameError || isJust mContractIdError
              , onClick_ $ AddNewWallet mTokenName
              ]
              [ text "Save" ]
          ]
      ]

walletDetailsCard :: forall p a. WalletDetails -> HTML p a
walletDetailsCard walletDetails =
  let
    nickname = view _nickname walletDetails

    contractId = view _contractId walletDetails
  in
    div_
      [ h3
          [ classNames [ "font-bold", "mb-4" ] ]
          [ text $ "Wallet " <> nickname ]
      , div
          [ classNames Css.hasNestedLabel ]
          [ label
              [ classNames Css.nestedLabel ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ Css.input false <> [ "mb-4" ]
              , value contractId
              , readOnly true
              ]
          ]
      ]

putdownWalletCard :: forall p. WalletDetails -> HTML p Action
putdownWalletCard walletDetails =
  let
    nickname = view _nickname walletDetails

    contractId = view _contractId walletDetails
  in
    div_
      [ h3
          [ classNames [ "font-bold", "mb-4" ] ]
          [ text $ "Wallet " <> nickname ]
      , div
          [ classNames Css.hasNestedLabel ]
          [ label
              [ classNames Css.nestedLabel ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ Css.input false <> [ "mb-4" ]
              , value contractId
              , readOnly true
              ]
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
              , onClick_ $ SetCard Nothing
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
        [ classNames [ "font-bold", "mb-4" ] ]
        [ text "Contacts" ]
    , if isEmpty library then
        p_ [ text "You do not have any contacts." ]
      else
        ul_
          $ contactLi
          <$> toUnfoldable library
    , button
        [ classNames $ Css.primaryButton <> Css.withIcon Add <> Css.fixedBottomRight
        , onClick_ $ ToggleCard $ CreateWalletCard Nothing
        ]
        [ text "New contact" ]
    ]
  where
  contactLi (Tuple nickname walletDetails) =
    let
      contractId = view _contractId walletDetails
    in
      li
        [ classNames [ "mt-4", "hover:cursor-pointer", "hover:text-green" ]
        , onClick_ $ ToggleCard $ ViewWalletCard walletDetails
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
