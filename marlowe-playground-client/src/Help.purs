module Help where

import Data.Array as Array
import Data.Map as Map
import Data.Maybe (Maybe)
import Data.String (fromCodePointArray, toCodePointArray)
import Halogen.Classes (readMoreIconWhite)
import Halogen.HTML (ClassName(..), HTML, div, h4, hr, img, p_, text)
import Halogen.HTML.Properties (alt, class_, src)
import Marlowe.Holes (MarloweType(..))
import Marlowe.Holes as Holes
import Prelude (show, (<<<), (<>), (<$>))
import Types (HelpContext(..))

toHTML :: forall p a. HelpContext -> Array (HTML p a)
toHTML helpType =
  [ div [ class_ (ClassName "help-title") ]
      [ img [ src readMoreIconWhite, alt "read more icon" ]
      , h4 [] [ headerText helpType ]
      ]
  , hr []
  , p_ [ bodyText helpType ]
  ]
  where
  headerText MarloweHelp = text "Modelling contracts in Marlowe"

  headerText InputComposerHelp = text "Input Composer"

  headerText TransactionComposerHelp = text "Transaction Composer"

  bodyText MarloweHelp = text "Marlowe is designed to support the execution of financial contracts on blockchain, and specifically to work on Cardano. Contracts are built by putting together a small number of constructs that in combination can be used to describe many different kinds of financial contract"

  bodyText InputComposerHelp = text "The Input Composer allows you to choose any of the possible inputs to add to a transaction"

  bodyText TransactionComposerHelp = text "The transaction composer shows you the contents of a transaction which is ready to apply. The inputs within a transaction are applied in order."

holeText :: MarloweType -> String
holeText marloweType = "Found a hole of type " <> dropEnd 4 (show marloweType) <> "\n" <> text <> "\nClick on Quick Fix below to see the options."
  where
  text = marloweTypeMarkerText marloweType

  dropEnd :: Int -> String -> String
  dropEnd n = fromCodePointArray <<< Array.dropEnd n <<< toCodePointArray

marloweTypeMarkerText :: MarloweType -> String
marloweTypeMarkerText AccountIdType =
  """
The Marlowe model allows for a contract to control money in a number of disjoint accounts: this allows for more explicit control of how the money flows in the contract. Each account is owned by a particular party to the contract, and that party receives a refund of any remaining funds in the account when the contract is closed. These accounts are local, in that they only exist as during the execution of the contract, and during that time they are only accessible by parties to the contract.
"""

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
