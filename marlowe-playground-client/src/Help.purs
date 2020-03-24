module Help where

import Halogen.Classes (mAlignCenter, readMoreIconWhite, tAlignCenter)
import Halogen.HTML (HTML, h4, hr, img, p_, text)
import Halogen.HTML.Properties (alt, class_, src)
import Types (HelpContext(..))

toHTML :: forall p a. HelpContext -> Array (HTML p a)
toHTML MarloweHelp =
  [ img [ class_ mAlignCenter, src readMoreIconWhite, alt "read more icon" ]
  , h4 [ class_ tAlignCenter ] [ text "Modelling contracts in Marlowe" ]
  , hr []
  , p_ [ text "Marlowe is designed to support the execution of financial contracts on blockchain, and specifically to work on Cardano. Contracts are built by putting together a small number of constructs that in combination can be used to describe many different kinds of financial contract" ]
  ]

toHTML InputComposerHelp =
  [ img [ class_ mAlignCenter, src readMoreIconWhite, alt "read more icon" ]
  , h4 [ class_ tAlignCenter ] [ text "Input Composer" ]
  , hr []
  , p_ [ text "Something about the Input Composer" ]
  ]

toHTML TransactionComposerHelp =
  [ img [ class_ mAlignCenter, src readMoreIconWhite, alt "read more icon" ]
  , h4 [ class_ tAlignCenter ] [ text "Transaction Composer" ]
  , hr []
  , p_ [ text "Something about the transaction composer" ]
  ]
