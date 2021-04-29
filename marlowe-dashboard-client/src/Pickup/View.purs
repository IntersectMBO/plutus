module Pickup.View (renderPickupState) where

import Prelude hiding (div)
import Css (classNames)
import Css as Css
import Data.Foldable (foldMap)
import Data.Lens (view)
import Data.Maybe (isJust, isNothing)
import Data.Newtype (unwrap)
import Data.UUID (toString) as UUID
import Halogen.HTML (HTML, a, button, div, div_, footer, header, hr, img, input, label, main, p, span_, text)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), disabled, for, href, id_, list, placeholder, readOnly, src, type_, value)
import Logo (marloweRunLogo)
import Material.Icons (Icon(..), icon, icon_)
import Pickup.Lenses (_card, _pickingUp, _pickupWalletString, _walletDetails, _walletLibrary)
import Pickup.Types (Action(..), Card(..), State)
import Prim.TypeError (class Warn, Text)
import WalletData.Lenses (_companionContractId, _walletNickname)
import WalletData.Validation (walletNicknameError)
import WalletData.View (nicknamesDataList)

renderPickupState :: forall p. State -> HTML p Action
renderPickupState state =
  div
    [ classNames [ "grid", "h-full" ] ]
    [ main
        [ classNames [ "relative" ] ]
        -- In the Play view, there are potentially many cards all inside a containing div,
        -- and the last one has a semi-transparent overlay (using class "last:bg-overlay").
        -- Here in the Pickup view there is at most one card, but we need to put it inside
        -- a containing div as well, so that it's the last child, and has the bg-overlay
        -- applied.
        [ div_ [ renderPickupCard state ]
        , renderPickupScreen state
        ]
    ]

------------------------------------------------------------
renderPickupCard :: forall p. State -> HTML p Action
renderPickupCard state =
  let
    card = view _card state
  in
    div
      [ classNames $ Css.overlay $ isNothing card ]
      [ div
          [ classNames $ Css.card $ isNothing card ]
          $ (flip foldMap card) \cardType -> case cardType of
              PickupNewWalletCard -> pickupNewWalletCard state
              PickupWalletCard -> pickupWalletCard state
              LocalWalletMissingCard -> localWalletMissingCard
      ]

pickupNewWalletCard :: forall p. State -> Array (HTML p Action)
pickupNewWalletCard state =
  let
    walletLibrary = view _walletLibrary state

    walletDetails = view _walletDetails state

    pickingUp = view _pickingUp state

    walletNickname = view _walletNickname walletDetails

    contractInstanceId = view _companionContractId walletDetails

    mWalletNicknameError = walletNicknameError walletNickname walletLibrary
  in
    [ a
        [ classNames [ "absolute", "top-4", "right-4" ]
        , onClick_ CloseCard
        ]
        [ icon_ Close ]
    , div [ classNames [ "p-5", "pb-6", "md:pb-8" ] ]
        [ p
            [ classNames [ "font-bold", "mb-4" ] ]
            [ text $ "Demo wallet generated" ]
        , div
            [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
            $ [ label
                  [ classNames $ Css.nestedLabel
                  , for "newWalletNickname"
                  ]
                  [ text "Nickname" ]
              , input
                  $ [ type_ InputText
                    , classNames $ (Css.input $ isJust mWalletNicknameError) <> [ "text-lg" ]
                    , id_ "newWalletNickname"
                    , placeholder "Nickname"
                    , value walletNickname
                    , onValueInput_ SetWalletNickname
                    ]
              , div
                  [ classNames Css.inputError ]
                  [ text $ foldMap show mWalletNicknameError ]
              ]
        , div
            [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
            [ label
                [ classNames Css.nestedLabel
                , for "newWalletID"
                ]
                [ text "Wallet ID" ]
            , input
                [ type_ InputText
                , classNames $ (Css.input false) <> [ "text-lg" ]
                , id_ "newWalletID"
                , value $ UUID.toString $ unwrap contractInstanceId
                , readOnly true
                ]
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
                , disabled $ isJust mWalletNicknameError || pickingUp
                , onClick_ PickupWallet
                ]
                [ text if pickingUp then "Picking up... " else "Pickup" ]
            ]
        ]
    ]

pickupWalletCard :: forall p. State -> Array (HTML p Action)
pickupWalletCard state =
  let
    pickingUp = view _pickingUp state

    walletDetails = view _walletDetails state

    walletNickname = view _walletNickname walletDetails

    companionContractId = view _companionContractId walletDetails
  in
    [ a
        [ classNames [ "absolute", "top-4", "right-4" ]
        , onClick_ CloseCard
        ]
        [ icon_ Close ]
    , div [ classNames [ "p-5", "pb-6", "md:pb-8" ] ]
        [ p
            [ classNames [ "font-bold", "mb-4" ] ]
            [ text $ "Play wallet " <> walletNickname ]
        , div
            [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
            $ [ label
                  [ classNames $ Css.nestedLabel
                  , for "nickname"
                  ]
                  [ text "Nickname" ]
              , input
                  $ [ type_ InputText
                    , classNames $ Css.input false
                    , id_ "nickname"
                    , value walletNickname
                    , readOnly true
                    ]
              ]
        , div
            [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
            [ label
                [ classNames Css.nestedLabel
                , for "walletId"
                ]
                [ text "Wallet ID" ]
            , input
                [ type_ InputText
                , classNames $ Css.input false
                , id_ "walletId"
                , value $ UUID.toString $ unwrap companionContractId
                , readOnly true
                ]
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
                , onClick_ PickupWallet
                , disabled pickingUp
                ]
                [ text if pickingUp then "Picking up... " else "Pickup" ]
            ]
        ]
    ]

localWalletMissingCard :: forall p. Array (HTML p Action)
localWalletMissingCard =
  [ a
      [ classNames [ "absolute", "top-4", "right-4" ]
      , onClick_ CloseCard
      ]
      [ icon_ Close ]
  , div [ classNames [ "flex", "font-semibold", "px-5", "py-4", "bg-gray" ] ]
      [ icon ErrorOutline [ "mr-2" ]
      , span_ [ text "Wallet not found" ]
      ]
  , div
      [ classNames [ "p-5", "pb-6", "md:pb-8" ] ]
      [ p
          [ classNames [ "mb-4" ] ]
          [ text "A wallet that you have previously used is no longer available in our demo server. This is probably because the demo server has been updated. (Note that this demo is in continuous development, and data is not preserved between updates.) We recommend that you use the button below to clear your browser's cache for this site and start again." ]
      , div
          [ classNames [ "flex", "justify-center" ] ]
          [ button
              [ classNames Css.primaryButton
              , onClick_ ClearLocalStorage
              ]
              [ text "Clear Cache" ]
          ]
      ]
  ]

------------------------------------------------------------
renderPickupScreen :: forall p. Warn (Text "We need to add the Marlowe links.") => State -> HTML p Action
renderPickupScreen state =
  div
    [ classNames [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "overflow-auto", "z-0", "flex", "flex-col", "justify-between" ] ]
    [ header
        [ classNames [ "flex" ] ]
        [ link "marlowe.io" "" ]
    , pickupWalletScreen state
    , footer
        [ classNames [ "flex", "justify-between" ] ]
        [ link "Docs" ""
        , link "Marketplace" ""
        ]
    ]

pickupWalletScreen :: forall p. State -> HTML p Action
pickupWalletScreen state =
  let
    walletLibrary = view _walletLibrary state

    pickupWalletString = view _pickupWalletString state
  in
    main
      [ classNames [ "p-4", "max-w-sm", "mx-auto", "text-center" ] ]
      [ img
          [ classNames [ "w-4/5", "mx-auto", "mb-6" ]
          , src marloweRunLogo
          ]
      , p
          [ classNames [ "mb-4" ] ]
          [ text "To use Marlowe Run, generate a new demo wallet." ]
      , button
          [ classNames $ Css.primaryButton <> [ "w-full", "text-center", "mb-4" ]
          , onClick_ GenerateWallet
          ]
          [ text "Generate demo wallet" ]
      , hr [ classNames [ "mb-4", "max-w-xs", "mx-auto" ] ]
      , p
          [ classNames [ "mb-4" ] ]
          [ text "Or use an existing one by selecting from the list or typing a public key or nickname." ]
      , input
          [ type_ InputText
          , classNames $ Css.inputCard false
          , id_ "existingWallet"
          , list "walletNicknames"
          , placeholder "Choose or input key/nickname"
          , value pickupWalletString
          , onValueInput_ SetPickupWalletString
          ]
      , nicknamesDataList walletLibrary
      ]

link :: forall p a. String -> String -> HTML p a
link label url =
  a
    [ classNames [ "flex", "items-center", "p-2", "font-bold" ]
    , href url
    ]
    [ text label ]
