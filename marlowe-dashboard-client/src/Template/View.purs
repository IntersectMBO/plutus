module Template.View
  ( contractSetupScreen
  , templateLibraryCard
  , contractSetupConfirmationCard
  ) where

import Prelude hiding (div)
import Css (applyWhen, classNames, hideWhen)
import Css as Css
import Data.Array (mapWithIndex)
import Data.BigInteger (fromString) as BigInteger
import Data.Lens (view)
import Data.Map (Map, lookup)
import Data.Map (toUnfoldable) as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Set (toUnfoldable) as Set
import Data.String (null)
import Data.Tuple.Nested ((/\))
import Halogen.HTML (HTML, a, br_, button, div, h2, hr, input, label, li, p_, span, span_, text, ul, ul_)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), for, id_, list, placeholder, readOnly, type_, value)
import Marlowe.Extended (Contract, TemplateContent, _valueContent, contractTypeInitials)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.HasParties (getParties)
import Marlowe.Semantics (Party(..), Slot)
import Material.Icons (Icon(..), icon_)
import Template.Lenses (_contractName, _contractNickname, _extendedContract, _metaData, _roleWallets, _slotContentStrings, _template, _templateContent)
import Template.Types (Action(..), State)
import Template.Validation (roleError, roleWalletsAreValid, slotError, templateContentIsValid, valueError)
import WalletData.Types (WalletLibrary)
import WalletData.View (nicknamesDataList)

contractSetupScreen :: forall p. WalletLibrary -> Slot -> State -> HTML p Action
contractSetupScreen wallets currentSlot state =
  let
    metaData = view (_template <<< _metaData) state

    contractName = view (_contractName) metaData

    extendedContract = view (_template <<< _extendedContract) state

    contractNickname = view _contractNickname state

    roleWallets = view _roleWallets state

    templateContent = view _templateContent state

    slotContentStrings = view _slotContentStrings state

    termsAreAccessible = roleWalletsAreValid roleWallets wallets

    payIsAccessible = termsAreAccessible && templateContentIsValid templateContent slotContentStrings currentSlot
  in
    div
      [ classNames [ "grid", "grid-rows-contract-setup", "h-full", "overflow-hidden" ] ]
      [ navigationBar contractName
      , contractNicknameDisplay contractName contractNickname
      , div -- the containing grid sets the height of this div
          [ classNames [ "px-3", "md:px-5pc" ] ]
          [ div -- and then this fills that height fully
              [ classNames [ "h-full", "overflow-y-auto" ] ]
              [ subHeader "top-0" true Roles "Roles" true
              , roleInputs wallets extendedContract metaData roleWallets
              , subHeader "top-12" true Terms "Terms" termsAreAccessible
              , parameterInputs wallets currentSlot metaData templateContent slotContentStrings roleWallets termsAreAccessible
              , subHeader "top-24" false Pay "Review and pay" payIsAccessible
              , reviewAndPay payIsAccessible metaData
              ]
          ]
      ]

navigationBar :: forall p. String -> HTML p Action
navigationBar contractName =
  div
    [ classNames [ "flex", "justify-between", "items-center", "px-3", "py-2", "border-b", "border-gray", "md:px-5pc" ] ]
    [ a
        -- "-ml-1" makes the icon line up properly
        [ classNames [ "flex", "items-center", "font-semibold", "-ml-1" ]
        , onClick_ ToggleTemplateLibraryCard
        ]
        [ icon_ Previous
        , span_
            [ text "Choose template" ]
        ]
    , span
        [ classNames [ "text-sm", "uppercase" ] ]
        [ text contractName ]
    ]

contractNicknameDisplay :: forall p. String -> String -> HTML p Action
contractNicknameDisplay contractName contractNickname =
  div
    [ classNames [ "px-3", "md:px-5pc" ] ]
    [ div
        [ classNames [ "ml-4", "border-l", "border-gray", "lg:ml-0", "lg:border-0" ] ]
        [ div
            [ classNames [ "max-w-sm", "lg:w-sm", "mx-auto", "px-3", "pt-2", "pb-1" ] ]
            [ input
                [ classNames $ (Css.input $ null contractNickname) <> [ "bg-transparent", "font-semibold" ]
                , type_ InputText
                , placeholder "Contract name *"
                , value contractNickname
                , onValueInput_ SetContractNickname
                ]
            ]
        ]
    ]

subHeader :: forall p. String -> Boolean -> Icon -> String -> Boolean -> HTML p Action
subHeader topMargin border i title accessible =
  div
    [ classNames $ [ "ml-4", "sticky", "z-10", topMargin, "pb-1", "bg-grayblue" ] <> applyWhen border [ "border-l", "border-gray" ] ]
    [ div
        [ classNames [ "flex", "items-center" ] ]
        [ span
            [ classNames $ Css.iconCircle accessible <> [ "-ml-3" ] ]
            [ icon_ i ]
        , h2
            [ classNames [ "py-1", "px-2", "text-lg", "font-semibold" ] ]
            [ text title ]
        , hr [ classNames $ [ "flex-1" ] <> hideWhen (not accessible) ]
        ]
    ]

roleInputs :: forall p. WalletLibrary -> Contract -> MetaData -> Map String String -> HTML p Action
roleInputs wallets extendedContract metaData roleWallets =
  subSection true true
    [ ul_
        $ mapWithIndex partyInput
        $ Set.toUnfoldable
        $ getParties extendedContract
    ]
  where
  partyInput index (PK pubKey) =
    li
      [ classNames [ "mb-2", "last:mb-0" ] ]
      [ label
          [ classNames [ "block", "text-sm" ]
          , for pubKey
          ]
          [ text $ "Party " <> (show $ index + 1) ]
      , input
          [ classNames $ Css.input false <> [ "shadow" ]
          , id_ pubKey
          , type_ InputText
          , value pubKey
          , readOnly true
          ]
      ]

  partyInput index (Role tokenName) =
    let
      description = fromMaybe "no description available" $ lookup tokenName metaData.roleDescriptions

      assigned = fromMaybe "" $ lookup tokenName roleWallets

      mRoleError = roleError assigned wallets
    in
      li
        [ classNames [ "mb-2", "last:mb-0" ] ]
        [ label
            [ classNames [ "block", "text-sm" ]
            , for tokenName
            ]
            [ span
                [ classNames [ "font-bold" ] ]
                [ text $ "Role " <> (show $ index + 1) <> " (" <> tokenName <> ")*" ]
            , br_
            , text description
            ]
        , div
            [ classNames [ "relative" ] ]
            [ input
                [ classNames $ Css.input (isJust mRoleError) <> [ "shadow", "pr-9" ]
                , id_ tokenName
                , type_ InputText
                , list "walletNicknames"
                , onValueInput_ $ SetRoleWallet tokenName
                , value assigned
                ]
            , button
                [ classNames [ "absolute", "top-3", "right-3" ]
                , onClick_ $ ToggleCreateWalletCard tokenName
                ]
                [ icon_ AddCircle ]
            ]
        , div
            [ classNames Css.inputError ]
            $ case mRoleError of
                Just roleError -> [ text $ show roleError ]
                Nothing -> []
        , nicknamesDataList wallets
        ]

parameterInputs :: forall p. WalletLibrary -> Slot -> MetaData -> TemplateContent -> Map String String -> Map String String -> Boolean -> HTML p Action
parameterInputs wallets currentSlot metaData templateContent slotContentStrings roleWallets accessible =
  let
    valueContent = view _valueContent templateContent
  in
    subSection accessible true
      [ ul
          [ classNames [ "mb-4" ] ]
          $ mapWithIndex slotInput (Map.toUnfoldable slotContentStrings)
      , ul_
          $ mapWithIndex valueInput (Map.toUnfoldable valueContent)
      ]
  where
  slotInput index (key /\ dateTimeString) =
    let
      description = fromMaybe "no description available" $ lookup key metaData.slotParameterDescriptions

      mParameterError = slotError dateTimeString currentSlot
    in
      li
        [ classNames [ "mb-4", "last:mb-0" ] ]
        [ label
            [ classNames [ "block", "text-sm" ]
            , for $ "slot-" <> key
            ]
            [ span
                [ classNames [ "font-bold" ] ]
                [ text $ "Timeout " <> (show $ index + 1) <> " (" <> key <> ")*" ]
            , br_
            , text description
            ]
        , input
            [ classNames $ Css.input (isJust mParameterError) <> [ "shadow" ]
            , id_ $ "slot-" <> key
            , type_ InputDatetimeLocal
            , onValueInput_ $ SetSlotContent key
            , value dateTimeString
            ]
        , div
            [ classNames Css.inputError ]
            $ case mParameterError of
                Just parameterError -> [ text $ show parameterError ]
                Nothing -> []
        ]

  valueInput index (key /\ parameterValue) =
    let
      description = fromMaybe "no description available" $ lookup key metaData.valueParameterDescriptions

      mParameterError = valueError parameterValue
    in
      li
        [ classNames [ "mb-4", "last:mb-0" ] ]
        [ label
            [ classNames [ "block", "text-sm" ]
            , for $ "value-" <> key
            ]
            [ span
                [ classNames [ "font-bold" ] ]
                [ text $ "Value " <> (show $ index + 1) <> " (" <> key <> ")*" ]
            , br_
            , text description
            ]
        , input
            [ classNames $ Css.input (isJust mParameterError) <> [ "shadow" ]
            , id_ $ "value-" <> key
            , type_ InputNumber
            , onValueInput_ $ SetValueContent key <<< BigInteger.fromString
            , value $ show parameterValue
            ]
        , div
            [ classNames Css.inputError ]
            $ case mParameterError of
                Just parameterError -> [ text $ show parameterError ]
                Nothing -> []
        ]

reviewAndPay :: forall p. Boolean -> MetaData -> HTML p Action
reviewAndPay accessible metaData =
  subSection accessible false
    [ div
        [ classNames $ [ "mb-4", "bg-white", "p-4", "shadow", "rounded" ] ]
        [ contractTitle metaData ]
    , div
        [ classNames [ "flex", "justify-end", "mb-4" ] ]
        [ button
            [ classNames Css.primaryButton
            , onClick_ $ ToggleSetupConfirmationCard
            ]
            [ text "Pay" ]
        ]
    ]

subSection :: forall p. Boolean -> Boolean -> Array (HTML p Action) -> HTML p Action
subSection accessible border content =
  div
    [ classNames $ [ "py-2", "ml-4", "mb-1" ] <> applyWhen border [ "border-l", "border-gray" ] <> (hideWhen $ not accessible) ]
    [ div
        [ classNames $ [ "max-w-sm", "mx-auto", "px-3" ] ]
        content
    ]

------------------------------------------------------------
templateLibraryCard :: forall p. Array ContractTemplate -> HTML p Action
templateLibraryCard templates =
  div
    [ classNames [ "md:px-5pc" ] ]
    [ h2
        [ classNames [ "text-lg", "font-semibold", "mt-2", "mb-4" ] ]
        [ text "Choose a contract template" ]
    , div
        [ classNames [ "grid", "gap-4", "md:grid-cols-2", "xl:grid-cols-3" ] ]
        (templateBox <$> templates)
    ]
  where
  templateBox template =
    div
      [ classNames [ "bg-white", "p-4" ] ]
      [ div
          [ classNames [ "flex", "justify-between", "items-start", "mb-4" ] ]
          [ contractTitle template.metaData
          , button
              [ classNames $ Css.primaryButton <> Css.withIcon ArrowRight <> [ "min-w-button-min" ]
              , onClick_ $ SetTemplate template
              ]
              [ text "Setup" ]
          ]
      , p_
          [ text template.metaData.contractDescription ]
      ]

contractTitle :: forall p. MetaData -> HTML p Action
contractTitle metaData =
  div
    [ classNames [ "flex", "items-start", "leading-none", "mr-1" ] ]
    [ span
        [ classNames [ "text-2xl", "font-semibold", "mr-2" ] ]
        [ text $ contractTypeInitials metaData.contractType ]
    , span
        [ classNames [ "text-sm", "pt-1", "uppercase" ] ]
        [ text $ metaData.contractName ]
    ]

contractSetupConfirmationCard :: forall p. HTML p Action
contractSetupConfirmationCard =
  div [ classNames [ "px-4", "pb-4" ] ]
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
