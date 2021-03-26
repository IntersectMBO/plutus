module View.Blockchain (annotatedBlockchainPane) where

import Bootstrap (cardBody_, cardHeader_, card_)
import Cardano.Metadata.Types (Subject(..))
import Chain.Types as Chain
import Chain.View (chainView)
import Data.Array as Array
import Data.Map as Map
import Data.Maybe (Maybe(Nothing))
import Data.Newtype (wrap)
import Halogen.HTML (HTML, h2_, text)
import Plutus.V1.Ledger.Crypto (PubKeyHash(..))
import Plutus.PAB.Webserver.Types (ChainReport(..))
import Prelude (bind)
import Types (propertyName)

annotatedBlockchainPane :: forall p. Chain.State -> ChainReport -> HTML p Chain.Action
annotatedBlockchainPane chainState (ChainReport { annotatedBlockchain }) =
  card_
    [ cardHeader_
        [ h2_ [ text "Blockchain" ]
        ]
    , cardBody_
        [ chainView namingFn chainState (wrap annotatedBlockchain)
        ]
    ]
  where
  namingFn (PubKeyHash { getPubKeyHash: hash }) = Nothing
