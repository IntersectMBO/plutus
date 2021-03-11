module Template.View
  ( contractSetupScreen
  , templateLibraryCard
  , contractSetupConfirmationCard
  ) where

import Prelude hiding (div, min)
import Css (applyWhen, classNames)
import Css as Css
import Data.BigInteger (fromString) as BigInteger
import Data.Lens (view)
import Data.Map (Map, lookup)
import Data.Map (toUnfoldable) as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Set (toUnfoldable) as Set
import Data.Tuple.Nested ((/\))
import Halogen.HTML (HTML, a, button, div, div_, h2, hr, input, label, li, p_, span, span_, text, ul, ul_)
import Halogen.HTML.Events (onBlur)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), autofocus, enabled, for, id_, list, min, placeholder, readOnly, type_, value)
import Marlowe.Extended (Contract, ContractTemplate, IntegerTemplateType(..), MetaData, TemplateContent, _slotContent, _valueContent, contractTypeInitials, getParties)
import Marlowe.Semantics (PubKey, Party(..))
import Material.Icons as Icon
import Template.Lenses (_contractName, _contractNickname, _editingNickname, _extendedContract, _metaData, _roleWallets, _setupProgress, _template, _templateContent)
import Template.Types (Action(..), SetupProgress(..), State)
import Template.Validation (roleError, roleWalletsAreValid, slotError, valueError)
import WalletData.Types (WalletLibrary)
import WalletData.View (nicknamesDataList)

contractSetupScreen :: forall p. WalletLibrary -> State -> HTML p Action
contractSetupScreen wallets state =
  let
    metaData = view (_template <<< _metaData) state

    contractName = view (_contractName) metaData

    extendedContract = view (_template <<< _extendedContract) state

    contractNickname = view _contractNickname state

    roleWallets = view _roleWallets state

    templateContent = view _templateContent state

    editingNickname = view _editingNickname state

    setupProgress = view _setupProgress state
  in
    div
      [ classNames [ "grid", "grid-rows-contract-setup", "h-full", "overflow-hidden" ] ]
      [ div
          [ classNames [ "border-b", "border-darkgray", "bg-grayblue" ] ]
          [ a
              [ classNames [ "flex", "items-center", "p-2", "font-semibold" ]
              , onClick_ ToggleTemplateLibraryCard
              ]
              [ Icon.previous
              , span_
                  [ text "Choose template" ]
              ]
          ]
      , contractNicknameDisplay contractName contractNickname editingNickname
      , div
          [ classNames [ "h-full", "overflow-y-auto", "grid" ] ]
          [ subHeader "top-0" Icon.roles "Roles"
          , contractRoles wallets metaData extendedContract roleWallets
          , subHeader "top-10" Icon.terms "Terms"
          , contractParameters metaData templateContent
          , subHeader "top-20" Icon.pay "Review and pay"
          , contractReview state
          ]
      ]

contractNicknameDisplay :: forall p. String -> String -> Boolean -> HTML p Action
contractNicknameDisplay contractName contractNickname editingNickname =
  div
    [ classNames [ "ml-12", "border-l", "border-darkgray", "p-2", "pl-6" ] ]
    [ div
        [ classNames [] ]
        [ div
            [ classNames [ "uppercase", "text-sm" ] ]
            [ text contractName ]
        , if editingNickname then
            input
              [ classNames [ "bg-transparent", "font-semibold" ]
              , type_ InputText
              , placeholder "Contract name"
              , value contractNickname
              , onValueInput_ SetContractNickname
              , onBlur $ const $ Just ToggleEditingNickname
              ]
          else
            div_
              [ span
                  [ classNames [ "font-semibold", "mr-2" ] ]
                  [ text contractNickname ]
              , a
                  [ classNames [ "inline-block", "-mt-4", "text-sm" ]
                  , onClick_ ToggleEditingNickname -- TODO: focus the nickname input
                  ]
                  [ text "edit" ]
              ]
        ]
    ]

subHeader :: forall p. String -> HTML p Action -> String -> HTML p Action
subHeader topMargin icon title =
  div
    [ classNames [ "sticky", topMargin, "ml-12", "border-l", "border-darkgray", "bg-grayblue" ] ]
    [ div
        [ classNames [ "flex", "items-center" ] ]
        [ span
            [ classNames $ Css.iconCircle <> [ "-ml-4" ] ]
            [ icon ]
        , h2
            [ classNames [ "p-2", "font-semibold" ] ]
            [ text title ]
        , hr [ classNames [ "flex-1" ] ]
        ]
    ]

contractRoles :: forall p. WalletLibrary -> MetaData -> Contract -> Map String PubKey -> HTML p Action
contractRoles wallets metaData extendedContract roleWallets =
  div
    [ classNames [ "ml-12", "border-l", "border-darkgray" ] ]
    [ ul
        [ classNames [ "mx-auto", "w-96" ] ]
        $ map partyInput (Set.toUnfoldable $ getParties extendedContract)
    ]
  where
  partyInput (PK pubKey) =
    li
      [ classNames [ "mb-4" ] ]
      [ label
          [ classNames [ "block", "mb-2" ]
          , for pubKey
          ]
          [ text "Wallet" ]
      , input
          [ classNames $ Css.input false <> [ "shadow" ]
          , id_ pubKey
          , type_ InputText
          , value pubKey
          , readOnly true
          ]
      ]

  partyInput (Role tokenName) =
    let
      description = fromMaybe "no description available" $ lookup tokenName metaData.roleDescriptions

      assigned = fromMaybe "" $ lookup tokenName roleWallets

      mRoleError = roleError assigned wallets
    in
      li
        [ classNames [ "mb-4" ] ]
        [ label
            [ classNames [ "block", "mb-2" ]
            , for tokenName
            ]
            [ text $ tokenName <> ": " <> description ]
        , input
            [ classNames $ Css.input (isJust mRoleError) <> [ "shadow" ]
            , id_ tokenName
            , type_ InputText
            , list "walletNicknames"
            , onValueInput_ $ SetRoleWallet tokenName
            , value assigned
            ]
        , div
            [ classNames Css.inputError ]
            $ case mRoleError of
                Just roleError -> [ text $ show roleError ]
                Nothing -> []
        , nicknamesDataList wallets
        ]

contractParameters :: forall p. MetaData -> TemplateContent -> HTML p Action
contractParameters metaData templateContent =
  let
    slotContent = view _slotContent templateContent

    valueContent = view _valueContent templateContent
  in
    div
      [ classNames [ "ml-12", "border-l", "border-darkgray" ] ]
      [ div
          [ classNames [ "mx-auto", "w-96" ] ]
          [ ul
              [ classNames [ "mb-4" ] ]
              $ map (parameterInput SlotContent) (Map.toUnfoldable slotContent)
          , ul_
              $ map (parameterInput ValueContent) (Map.toUnfoldable valueContent)
          ]
      ]
  where
  parameterInput integerTemplateType (key /\ parameterValue) =
    let
      description = case integerTemplateType of
        SlotContent -> fromMaybe "no description available" $ lookup key metaData.slotParameterDescriptions
        ValueContent -> fromMaybe "no description available" $ lookup key metaData.valueParameterDescriptions

      mParameterError = case integerTemplateType of
        SlotContent -> slotError parameterValue
        ValueContent -> valueError parameterValue
    in
      li
        [ classNames [ "mb-4" ] ]
        [ label
            [ classNames [ "block", "mb-2" ] ]
            [ text $ key <> ": " <> description ]
        , input
            [ classNames $ Css.input (isJust mParameterError) <> [ "shadow" ]
            , type_ InputNumber
            , min one
            , onValueInput_ $ SetParameter integerTemplateType key <<< BigInteger.fromString
            , value $ show parameterValue
            ]
        , div
            [ classNames Css.inputError ]
            $ case mParameterError of
                Just parameterError -> [ text $ show parameterError ]
                Nothing -> []
        ]

contractReview :: forall p. State -> HTML p Action
contractReview state =
  div
    [ classNames [ "ml-12", "border-l", "border-darkgray" ] ]
    [ div
        [ classNames [ "mx-auto", "w-96", "mb-4", "bg-white", "p-4", "shadow", "rounded-lg" ] ]
        [ text "Summary information about the contract goes here." ]
    ]

------------------------------------------------------------
templateLibraryCard :: forall p. Array ContractTemplate -> HTML p Action
templateLibraryCard templates =
  div_
    [ h2
        [ classNames [ "text-lg", "text-center", "font-semibold", "mb-4" ] ]
        [ text "Choose a contract template" ]
    , div
        [ classNames [ "grid", "gap-4", "md:grid-cols-2", "lg:grid-cols-3" ] ]
        (templateBox <$> templates)
    ]
  where
  templateBox template =
    div
      [ classNames [ "bg-white", "p-4" ] ]
      [ div
          [ classNames [ "flex", "justify-between", "mb-4" ] ]
          [ div
              [ classNames [ "flex", "align-top" ] ]
              [ span
                  [ classNames [ "text-2xl", "font-semibold", "mr-2" ] ]
                  [ text $ contractTypeInitials template.metaData.contractType ]
              , span
                  [ classNames [ "uppercase" ] ]
                  [ text $ template.metaData.contractName ]
              ]
          , button
              [ classNames Css.primaryButton
              , onClick_ $ SetTemplate template
              ]
              [ span_ [ text "Setup" ]
              , span_ [ Icon.next ]
              ]
          ]
      , p_
          [ text template.metaData.contractDescription ]
      ]

contractSetupConfirmationCard :: forall p. HTML p Action
contractSetupConfirmationCard =
  div_
    [ p_ [ text "Are you sure?" ]
    , div
        [ classNames [ "flex" ] ]
        [ button
            [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
            , onClick_ ToggleSetupConfirmationCard
            ]
            [ text "Cancel" ]
        , button
            [ classNames $ Css.primaryButton <> [ "flex-1" ]
            , onClick_ StartContract
            ]
            [ text "Pay" ]
        ]
    ]

{-
    , div
        [ classNames [ "flex", "justify-between" ] ]
        [ span
            [ classNames $ screenClasses setupScreen ContractRolesScreen ]
            [ text "Roles" ]
        , span
            [ classNames $ screenClasses setupScreen ContractParametersScreen ]
            [ text "Parameters" ]
        , span
            [ classNames $ screenClasses setupScreen ContractReviewScreen ]
            [ text "Review" ]
        ]
  where
  screenClasses currentScreen screen = [ "p-4" ] <> applyWhen (currentScreen == screen) [ "text-blue" ]


contractNavigationButtons :: forall p. Screen -> Map String String -> WalletLibrary -> Array (HTML p Action)
contractNavigationButtons screen roleWallets wallets = case screen of
  ContractRolesScreen ->
    [ a
        [ onClick_ ToggleTemplateLibraryCard ]
        [ text "< Library quick access" ]
    , button
        [ classNames Css.primaryButton
        , onClick_ $ SetScreen ContractParametersScreen
        , enabled $ roleWalletsAreValid roleWallets wallets
        ]
        [ text "Next >" ]
    ]
  ContractParametersScreen ->
    [ a
        [ onClick_ $ SetScreen ContractRolesScreen ]
        [ text "< Roles" ]
    , button
        [ classNames Css.primaryButton
        , onClick_ $ SetScreen ContractReviewScreen
        ]
        [ text "Next >" ]
    ]
  ContractReviewScreen ->
    [ a
        [ onClick_ $ SetScreen ContractParametersScreen ]
        [ text "< Parameters" ]
    , button
        [ classNames Css.primaryButton
        , onClick_ $ ToggleSetupConfirmationCard
        ]
        [ text "Pay and start >" ]
    ]

-}
