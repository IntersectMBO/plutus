module Marlowe.ViewPartials where

import Prelude hiding (div)
import Data.Array (mapWithIndex)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.Css (classNames)
import Halogen.HTML (ClassName(..), b_, div_, h4, li_, ol, text)
import Halogen.HTML.Properties (classes)
import Hint.State (hint)
import MainFrame.Types (ChildSlots)
import Marlowe.Semantics (Payee(..), TransactionWarning(..))
import Popper (Placement(..))
import Pretty (showPrettyToken)

displayWarningList ::
  forall m action.
  MonadAff m =>
  Array TransactionWarning ->
  ComponentHTML action ChildSlots m
displayWarningList transactionWarnings =
  ol [ classes [ ClassName "indented-enum" ] ]
    $ mapWithIndex
        (\index warning -> li_ $ displayWarning index warning)
        transactionWarnings

warningHint ::
  forall m action.
  MonadAff m =>
  Int ->
  String ->
  ComponentHTML action ChildSlots m
warningHint index msg =
  hint [ "ml-1", "relative", "-top-1" ] ("warning-" <> show index) Auto
    $ div_
        [ h4 [ classNames [ "no-margins", "text-lg", "font-semibold", "pb-2", "min-w-max" ] ]
            [ text "Warning" ]
        , text msg
        ]

displayWarning ::
  forall m action.
  MonadAff m =>
  Int ->
  TransactionWarning ->
  Array (ComponentHTML action ChildSlots m)
displayWarning index (TransactionNonPositiveDeposit party owner tok amount) =
  [ b_ [ text "Non-positive deposit" ]
  , warningHint index "A non-positive deposit is when the contract asks a participant to make a deposit of a value which is 0 or lower."
  , text " - Party "
  , b_ [ text $ show party ]
  , text " is asked to deposit "
  , b_ [ text $ show amount ]
  , text " units of "
  , b_ [ text $ showPrettyToken tok ]
  , text " into account of "
  , b_ [ text (show owner) ]
  , text "."
  ]

displayWarning index (TransactionNonPositivePay owner payee tok amount) =
  [ b_ [ text "Non-positive pay" ]
  , warningHint index "A non-positive pay is when the contract needs to pay a participant a value which is 0 or lower."
  , text " - The contract is supposed to make a payment of "
  , b_ [ text $ show amount ]
  , text " units of "
  , b_ [ text $ showPrettyToken tok ]
  , text " from account of "
  , b_ [ text (show owner) ]
  , text " to "
  , b_
      [ text case payee of
          (Account owner2) -> ("account of " <> (show owner2))
          (Party dest) -> ("party " <> (show dest))
      ]
  , text "."
  ]

displayWarning index (TransactionPartialPay owner payee tok amount expected) =
  [ b_ [ text "Partial pay" ]
  , warningHint index "A partial pay is when the contract needs to pay a participant a value grater than the funds available in the origin account."
  , text " - The contract is supposed to make a payment of "
  , b_ [ text $ show expected ]
  , text " units of "
  , b_ [ text $ showPrettyToken tok ]
  , text " from account of "
  , b_ [ text (show owner) ]
  , text " to "
  , b_
      [ text case payee of
          (Account owner2) -> ("account of " <> (show owner2))
          (Party dest) -> ("party " <> (show dest))
      ]
  , text " but there is only "
  , b_ [ text $ show amount ]
  , text "."
  ]

displayWarning index (TransactionShadowing valId oldVal newVal) =
  [ b_ [ text "Shadowing" ]
  , warningHint index "Shadowing is when a value is re-assigned to the same identifier, which means that we lose the reference to the previous value."
  , text " - The contract defined the value with id "
  , b_ [ text (show valId) ]
  , text " before, it was assigned the value "
  , b_ [ text (show oldVal) ]
  , text " and now it is being assigned the value "
  , b_ [ text (show newVal) ]
  , text "."
  ]

displayWarning index TransactionAssertionFailed =
  [ b_ [ text "Assertion failed" ]
  , text " - An assertion in the contract did not hold."
  ]
