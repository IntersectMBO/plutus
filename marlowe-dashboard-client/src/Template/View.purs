module Template.View
  ( contractSetupScreen
  , templateLibraryCard
  , contractSetupConfirmationCard
  ) where

import Prelude hiding (div)
import Css as Css
import Data.Array (mapWithIndex)
import Data.BigInteger (fromString) as BigInteger
import Data.Lens (view)
import Data.List (toUnfoldable) as List
import Data.Map (Map, lookup, values)
import Data.Map (toUnfoldable) as Map
import Data.Maybe (Maybe(..), fromMaybe, isNothing)
import Data.String (trim)
import Data.Tuple.Nested ((/\))
import Halogen.Css (applyWhen, classNames, hideWhen)
import Halogen.HTML (HTML, a, br_, button, div, div_, h2, hr, input, label, li, p, p_, span, span_, text, ul, ul_)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), enabled, for, id_, placeholder, type_, value)
import Humanize (humanizeValue)
import InputField.Types (State) as InputField
import InputField.Types (inputErrorToString)
import InputField.View (renderInput)
import Marlowe.Extended (contractTypeInitials)
import Marlowe.Extended.Metadata (MetaData, _contractName, _metaData, lovelaceFormat)
import Marlowe.Market (contractTemplates)
import Marlowe.PAB (contractCreationFee)
import Marlowe.Semantics (Assets, Slot, TokenName)
import Marlowe.Template (TemplateContent, _valueContent)
import Material.Icons (Icon(..), icon_)
import Template.Format (formatText)
import Template.Lenses (_contractNickname, _dummyNumberInput, _roleWalletInputs, _slotContentStrings, _template, _templateContent)
import Template.Types (Action(..), State)
import Template.Validation (RoleError, roleWalletsAreValid, slotError, templateContentIsValid, valueError)
import WalletData.Lenses (_walletNickname)
import WalletData.State (adaToken, getAda)
import WalletData.Types (WalletLibrary)

contractSetupScreen :: forall p. WalletLibrary -> Slot -> State -> HTML p Action
contractSetupScreen walletLibrary currentSlot state =
  let
    metaData = view (_template <<< _metaData) state

    contractName = view (_contractName) metaData

    contractNickname = view _contractNickname state

    roleWalletInputs = view _roleWalletInputs state

    templateContent = view _templateContent state

    slotContentStrings = view _slotContentStrings state

    termsAreAccessible = roleWalletsAreValid roleWalletInputs

    payIsAccessible = termsAreAccessible && templateContentIsValid templateContent slotContentStrings currentSlot

    dummyNumberInput = view _dummyNumberInput state

    dummyNumberInputOptions =
      { baseCss: Css.input
      , additionalCss: mempty
      , id_: "dummyNumber"
      , placeholder: mempty
      , readOnly: false
      , numberFormat: Just lovelaceFormat
      , valueOptions: mempty
      }
  in
    div
      [ classNames [ "grid", "grid-rows-contract-setup", "h-full", "overflow-hidden" ] ]
      [ navigationBar contractName
      , contractNicknameDisplay contractName contractNickname
      , div_ -- the containing grid sets the height of this div
          [ div -- and then this fills that height fully
              [ classNames [ "h-full", "overflow-y-auto", "px-4" ] ]
              [ DummyNumberInputAction <$> renderInput dummyNumberInputOptions dummyNumberInput
              , subHeader "top-0" true Roles "Roles" true
              , roleInputs walletLibrary metaData roleWalletInputs
              , subHeader "top-10" true Terms "Terms" termsAreAccessible
              , parameterInputs currentSlot metaData templateContent slotContentStrings termsAreAccessible
              , subHeader "top-20" false Pay "Review and pay" payIsAccessible
              , reviewAndPay payIsAccessible metaData
              ]
          ]
      ]

navigationBar :: forall p. String -> HTML p Action
navigationBar contractName =
  div
    [ classNames [ "flex", "justify-between", "items-center", "px-4", "py-2", "border-b", "border-gray" ] ]
    [ a
        -- "-ml-1" makes the icon line up properly
        [ classNames [ "flex", "items-center", "font-semibold", "-ml-1" ]
        , onClick_ OpenTemplateLibraryCard
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
    [ classNames [ "p-4" ] ]
    [ input
        [ classNames $ (Css.input $ contractNickname /= mempty) <> [ "font-semibold" ]
        , type_ InputText
        , placeholder "Contract name *"
        , value contractNickname
        , onValueInput_ SetContractNickname
        ]
    ]

subHeader :: forall p. String -> Boolean -> Icon -> String -> Boolean -> HTML p Action
subHeader topMargin border i title accessible =
  div
    [ classNames [ "mb-2" ] ]
    [ h2
        [ classNames [ "py-1", "px-2", "text-lg", "font-semibold" ] ]
        [ text title ]
    , hr [ classNames [ "flex-1" ] ]
    ]

-- We range over roleWalletInputs rather than all the parties in the contract. This excludes any `PK` parties.
-- At the moment, this is a good thing: we don't have a design for them, and we only use a `PK` party in one
-- special case, where it is read-only and would be confusing to show the user anyway. But if we ever need to
-- use `PK` inputs properly (and make them editable) we will have to rethink this.
roleInputs :: forall p. WalletLibrary -> MetaData -> Map TokenName (InputField.State RoleError) -> HTML p Action
roleInputs walletLibrary metaData roleWalletInputs =
  subSection true true
    [ ul_
        $ mapWithIndex roleInput
        $ Map.toUnfoldable roleWalletInputs
    ]
  where
  roleInput index (tokenName /\ roleWalletInput) =
    let
      description = fromMaybe "no description available" $ lookup tokenName metaData.roleDescriptions
    in
      li
        [ classNames [ "mb-2", "last:mb-0" ] ]
        [ label
            [ classNames [ "block", "text-sm", "mb-2" ]
            , for tokenName
            ]
            [ span
                [ classNames [ "font-bold" ] ]
                [ text $ "Role " <> (show $ index + 1) <> " (" <> tokenName <> ")*" ]
            , br_
            , span_ $ formatText description
            ]
        , div
            [ classNames [ "relative" ] ]
            [ RoleWalletInputAction tokenName <$> renderInput (roleWalletInputDisplayOptions tokenName) roleWalletInput
            , button
                [ classNames [ "absolute", "top-4", "right-4" ]
                , onClick_ $ OpenCreateWalletCard tokenName
                ]
                [ icon_ AddCircle ]
            ]
        ]

  roleWalletInputDisplayOptions tokenName =
    { baseCss: Css.inputCardNoFocus
    , additionalCss: [ "pr-9" ]
    , id_: tokenName
    , placeholder: "Choose any nickname"
    , readOnly: false
    , numberFormat: Nothing
    , valueOptions: List.toUnfoldable $ values $ view _walletNickname <$> walletLibrary
    }

parameterInputs :: forall p. Slot -> MetaData -> TemplateContent -> Map String String -> Boolean -> HTML p Action
parameterInputs currentSlot metaData templateContent slotContentStrings accessible =
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

      mParameterError = slotError currentSlot dateTimeString
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
            , span_ $ formatText description
            ]
        , input
            [ classNames $ Css.inputCard (isNothing mParameterError)
            , id_ $ "slot-" <> key
            , type_ InputDatetimeLocal
            , onValueInput_ $ SetSlotContent key
            , value dateTimeString
            ]
        , div
            [ classNames Css.inputError ]
            $ case mParameterError of
                Just parameterError -> [ text $ inputErrorToString parameterError ]
                Nothing -> []
        ]

  valueInput index (key /\ parameterValue) =
    let
      description =
        fromMaybe "no description available"
          ( case lookup key metaData.valueParameterInfo of
              Just { valueParameterDescription }
                | trim valueParameterDescription /= "" -> Just valueParameterDescription
              _ -> Nothing
          )

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
            , span_ $ formatText description
            ]
        , input
            [ classNames $ Css.inputCard (isNothing mParameterError)
            , id_ $ "value-" <> key
            , type_ InputNumber
            , onValueInput_ $ SetValueContent key <<< BigInteger.fromString
            , value $ show parameterValue
            ]
        , div
            [ classNames Css.inputError ]
            $ case mParameterError of
                Just parameterError -> [ text $ inputErrorToString parameterError ]
                Nothing -> []
        ]

reviewAndPay :: forall p. Boolean -> MetaData -> HTML p Action
reviewAndPay accessible metaData =
  subSection accessible false
    [ div
        [ classNames $ [ "mb-4", "bg-white", "p-4", "shadow", "rounded" ] ]
        [ contractTitle metaData
        , hr [ classNames [ "my-4" ] ]
        , div_
            [ p
                [ classNames [ "text-sm" ] ]
                [ text "Fee to pay:" ]
            , p
                [ classNames Css.funds ]
                [ text $ humanizeValue adaToken contractCreationFee ]
            ]
        ]
    , div
        [ classNames [ "flex", "justify-end", "mb-4" ] ]
        [ button
            [ classNames Css.primaryButton
            , onClick_ $ OpenSetupConfirmationCard
            ]
            [ text "Pay" ]
        ]
    ]

subSection :: forall p. Boolean -> Boolean -> Array (HTML p Action) -> HTML p Action
subSection accessible border content =
  div
    [ classNames $ [ "max-w-sm", "mx-auto", "px-4" ] ]
    content

------------------------------------------------------------
templateLibraryCard :: forall p. HTML p Action
templateLibraryCard =
  div
    [ classNames [ "p-4", "h-full", "overflow-y-auto" ] ]
    [ h2
        [ classNames [ "text-lg", "font-semibold", "mb-4" ] ]
        [ text "Choose a contract template" ]
    , div_ (templateBox <$> contractTemplates)
    ]
  where
  templateBox template =
    div
      [ classNames [ "bg-white", "p-4" ] ]
      [ div
          [ classNames [ "flex", "justify-between", "items-start", "mb-4" ] ]
          [ contractTitle template.metaData
          , button
              [ classNames $ Css.primaryButton <> Css.withIcon ArrowRight <> [ "min-w-button" ]
              , onClick_ $ SetTemplate template
              ]
              [ text "Setup" ]
          ]
      , p_ $ formatText template.metaData.contractDescription
      ]

-- TODO: This helper is really similar to contractCard in ContractHome.View, see if it makes sense to factor a component out
contractTitle :: forall p. MetaData -> HTML p Action
contractTitle metaData =
  div
    [ classNames [ "flex", "items-start", "mr-1" ] ]
    [ span
        [ classNames [ "text-2xl", "leading-none", "font-semibold" ] ]
        [ text $ contractTypeInitials metaData.contractType ]
    , span
        [ classNames [ "text-xs", "uppercase", "ml-2" ] ]
        [ text $ metaData.contractName ]
    ]

-- TODO: This is a lot like the `actionConfirmationCard` in `Contract.View`. Consider factoring out a shared component.
contractSetupConfirmationCard :: forall p. Assets -> HTML p Action
contractSetupConfirmationCard assets =
  let
    hasSufficientFunds = getAda assets >= contractCreationFee
  in
    div_
      [ div [ classNames [ "flex", "font-semibold", "justify-between", "bg-lightgray", "p-5" ] ]
          [ span_ [ text "Demo wallet balance:" ]
          , span_ [ text $ humanizeValue adaToken $ getAda assets ]
          ]
      , div [ classNames [ "px-5", "pb-6", "md:pb-8" ] ]
          [ p
              [ classNames [ "mt-4", "text-sm", "font-semibold" ] ]
              [ text "Confirm payment of:" ]
          , p
              [ classNames [ "mb-4", "text-purple", "font-semibold", "text-2xl" ] ]
              [ text $ humanizeValue adaToken contractCreationFee ]
          , div
              [ classNames [ "flex" ] ]
              [ button
                  [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-2" ]
                  , onClick_ CloseSetupConfirmationCard
                  ]
                  [ text "Cancel" ]
              , button
                  [ classNames $ Css.primaryButton <> [ "flex-1" ]
                  , onClick_ StartContract
                  , enabled hasSufficientFunds
                  ]
                  [ text "Pay and run" ]
              ]
          , div
              [ classNames [ "mt-4", "text-sm", "text-red" ] ]
              if hasSufficientFunds then
                []
              else
                [ text "You have insufficient funds to initialise this contract." ]
          ]
      ]
