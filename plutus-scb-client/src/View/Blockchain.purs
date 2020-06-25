module View.Blockchain (annotatedBlockchainPane) where

import Bootstrap (cardBody_, cardHeader_, card_)
import Chain.Types as Chain
import Chain.View (chainView)
import Data.Newtype (unwrap, wrap)
import Halogen.HTML (HTML, h2_, text)
import Plutus.SCB.Webserver.Types (ChainReport(..))

annotatedBlockchainPane :: forall t p. Chain.State -> ChainReport t -> HTML p Chain.Action
annotatedBlockchainPane chainState (ChainReport { walletMap, annotatedBlockchain }) =
  card_
    [ cardHeader_
        [ h2_ [ text "Blockchain" ]
        ]
    , cardBody_
        [ chainView chainState (unwrap walletMap) (wrap annotatedBlockchain)
        ]
    ]
