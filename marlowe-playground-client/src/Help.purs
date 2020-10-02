module Help where

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Map as Map
import Data.Maybe (Maybe)
import Data.String (fromCodePointArray, toCodePointArray)
import Halogen.Classes (blocklyIcon, readMoreIconWhite)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), HTML, div, h4, hr, img, p, p_, span, text)
import Halogen.HTML.Properties (alt, class_, src)
import Marlowe.Holes (MarloweType(..))
import Marlowe.Holes as Holes
import Prelude (class Show, show, (<$>), (<<<), (<>))

data HelpContext
  = MarloweHelp
  | InputComposerHelp
  | TransactionComposerHelp
  | AvailableActionsHelp
  | WalletsSimulatorHelp
  | EditorHelp

derive instance genericHelpContext :: Generic HelpContext _

instance showHelpContext :: Show HelpContext where
  show = genericShow

toHTML :: forall p a. HelpContext -> Array (HTML p a)
toHTML helpType =
  [ div [ class_ (ClassName "help-title") ]
      [ img [ src readMoreIconWhite, alt "read more icon" ]
      , h4 [] [ headerText helpType ]
      ]
  , hr []
  , p [ class_ (ClassName "help-body") ] [ bodyText helpType ]
  ]
  where
  headerText MarloweHelp = text "Modelling contracts in Marlowe"

  headerText InputComposerHelp = text "Input Composer"

  headerText TransactionComposerHelp = text "Transaction Composer"

  headerText AvailableActionsHelp = text "Available Actions"

  headerText WalletsSimulatorHelp = text "Wallets Simulator"

  headerText EditorHelp = text "Marlowe Code Editor"

  bodyText MarloweHelp = text "Marlowe is designed to support the execution of financial contracts on blockchain, and specifically to work on Cardano. Contracts are built by putting together a small number of constructs that in combination can be used to describe many different kinds of financial contract"

  bodyText InputComposerHelp = text "The Input Composer allows you to choose any of the possible inputs to add to a transaction"

  bodyText TransactionComposerHelp = text "The transaction composer shows you the contents of a transaction which is ready to apply. The inputs within a transaction are applied in order."

  bodyText AvailableActionsHelp = text "The available actions are actions which will progress the contract when applied. After an available action is applied, a new set of actions will be shown."

  bodyText WalletsSimulatorHelp = text "The Wallets Simulator allows you to see how your contract will look from the point of view of users. You can create multiple wallets then transfer roles, add assets and apply transactions in individual wallets. To get started create a wallet by clicking on the '+' button at the top of the main panel."

  bodyText EditorHelp =
    div []
      [ p_ [ text "Marlowe code can be edited and analysed in the code editor. To make things easier to read, you can format code at any time by right-clicking in the editor and selecting \"Format Document\"." ]
      , p_
          [ text
              "If you enter some invalid code, the code will be underlined in "
          , span [ class_ (ClassName "underline-red") ] [ text "red" ]
          , text
              ". You can hover over it for information about the error. Alternatively click on the "
          , bold "Errors"
          , text " tab in the bottom panel."
          ]
      , p_
          [ text "A valid contract can still contain parts that don't really make sense. Possible issues are underlined in "
          , code "yellow"
          , text " and again, hovering over them will display more information about the warning. These are displayed in full in the "
          , bold "Warnings"
          , text " tab in the bottom panel."
          ]
      , p_
          [ text "It is also possible to leave a "
          , code "hole"
          , text " in a contract where you are not sure what to fill in yet, you can do this by typing a "
          , code "?"
          , text " followed by a name, for example "
          , code "?next_contract."
          , text " This will also show up as a warning but in this case, when you hover over the warning you will be given a "
          , code "Quick Fix"
          , text " link. If you click "
          , code "Quick Fix"
          , text " then you will be given a list of options. You can also see these options by clicking on the \x1f4a1 symbol."
          ]
      , p_ [ text "The editor also has an auto-complete feature. Instead of writing a hole you can just press ctrl+space to show a list of possible values. You can also just start typing to see the options." ]
      , p_
          [ text "You can transfer a contract to blockly by clicking on the "
          , img [ class_ (ClassName "blockly-btn-inline-icon"), src blocklyIcon, alt "blockly logo" ]
          , text " button at the top-right of the editor. You cannot transfer a contract that has errors but warnings and holes are fine."
          ]
      , p_
          [ text "For more advanced users, the editor has key bindings for Vim and Emacs, you can select which mode you prefer from the drop-down list next to the "
          , img [ class_ (ClassName "blockly-btn-inline-icon"), src blocklyIcon, alt "blockly logo" ]
          , text " button."
          ]
      ]

code :: forall p a. String -> HTML p a
code s = span [ class_ (ClassName "inline-code") ] [ text s ]

bold :: forall p a. String -> HTML p a
bold s = span [ class_ Classes.bold ] [ text s ]

holeText :: MarloweType -> String
holeText marloweType = "Found a hole of type " <> dropEnd 4 (show marloweType) <> "\n" <> text <> "\nClick on Quick Fix below to see the options."
  where
  text = marloweTypeMarkerText marloweType

  dropEnd :: Int -> String -> String
  dropEnd n = fromCodePointArray <<< Array.dropEnd n <<< toCodePointArray

marloweTypeMarkerText :: MarloweType -> String
marloweTypeMarkerText ChoiceIdType =
  """
Choices – of integers – are identified by ChoiceId which combines a name for the choice with the Party who had made the choice
"""

marloweTypeMarkerText ValueIdType =
  """
Values defined using Let are identified by a ValueID
"""

marloweTypeMarkerText ActionType =
  """
Contracts in Marlowe run on a blockchain, but need to interact with the off-chain world. The parties to the contract, whom we also call the participants, can engage in various actions: they can be asked to deposit money, or to make a choice between various alternatives. A notification of an external value (also called an oracle value), such as the current price of a particular commodity, is the other possible form of input.
"""

marloweTypeMarkerText PayeeType =
  """
A payment contract will make a payment from an account to a Payee
"""

marloweTypeMarkerText CaseType =
  """
A When contract contains a collection of cases. Each case has the form `Case action next` where action is an Action and next a continuation (another contract). When a particular action happens, the state is updated accordingly and the contract will continue as the corresponding continuation `next`.
"""

marloweTypeMarkerText ValueType =
  """
A Value encompasses Ada, fungible tokens (think currencies), non-fungible tokens (a custom token that is not interchangeable with other tokens), and more exotic mixed cases.
"""

marloweTypeMarkerText ObservationType =
  """
Observations are Boolean values derived by comparing values, and can be combined using the standard Boolean operators. It is also possible to observe whether any choice has been made (for a particular identified choice).
"""

marloweTypeMarkerText ContractType =
  """
Marlowe has five ways of building contracts. Four of these – Pay, Let, If and When – build a complex contract from simpler contracts, and the fifth, Close, is a simple contract. At each step of execution, as well as returning a new state and continuation contract, it is possible that effects – payments – and warnings can be generated too.
"""

marloweTypeMarkerText BoundType =
  """
A choice is made for a particular id with a list of bounds on the values that are acceptable. For example, [Bound 0 0, Bound 3 5] offers the choice of one of 0, 3, 4 and 5.
"""

marloweTypeMarkerText TokenType =
  """
A Marlowe Account holds amounts of multiple currencies and/or fungible and non-fungible tokens. A concrete amount is indexed by a Token, which is a pair of CurrencySymbol and TokenName.
"""

marloweTypeMarkerText PartyType =
  """
A Party is represented as either a public key hash or a role name.
In order to progress a Marlowe contract, a party must provide an evidence. For PK party that would be a valid signature of a transaction signed by a private key of a public key that hashes to party’s PubKeyHash, similarly to Bitcoin’s Pay to Public Key Hash mechanism. For a Role party the evidence is spending a role token within the same transaction, usually to the same owner.

So, Role parties will look like (Role "alice"), (Role "bob") and so on.
"""

helpForConstructor :: String -> Maybe String
helpForConstructor constructor =
  let
    constructors = Holes.allMarloweConstructorNames

    marloweType = Map.lookup constructor constructors
  in
    marloweTypeMarkerText <$> marloweType
