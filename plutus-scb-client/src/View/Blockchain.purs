module View.Blockchain (annotatedBlockchainPane) where

import Bootstrap (cardBody_, cardHeader_, card_)
import Cardano.Metadata.Types (Subject(..))
import Chain.Types as Chain
import Chain.View (chainView)
import Data.Array as Array
import Data.Map as Map
import Data.Newtype (wrap)
import Halogen.HTML (HTML, h2_, text)
import Ledger.Crypto (PubKeyHash(..))
import Plutus.SCB.Webserver.Types (ChainReport(..))
import Prelude (bind)
import Types (propertyName)

annotatedBlockchainPane :: forall p. Chain.State -> ChainReport -> HTML p Chain.Action
annotatedBlockchainPane chainState (ChainReport { relatedMetadata, annotatedBlockchain }) =
  card_
    [ cardHeader_
        [ h2_ [ text "Blockchain" ]
        ]
    , cardBody_
        [ chainView namingFn chainState (wrap annotatedBlockchain)
        ]
    ]
  where
  namingFn (PubKeyHash { getPubKeyHash: hash }) = do
    properties <- Map.lookup (Subject hash) relatedMetadata
    Array.findMap propertyName properties
