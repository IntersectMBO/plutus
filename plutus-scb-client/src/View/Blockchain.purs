module View.Blockchain (annotatedBlockchainPane) where

import Bootstrap (cardBody_, cardHeader_, card_)
import Cardano.Metadata.Types (_Subject, propertySubject)
import Chain.Types as Chain
import Chain.View (chainView)
import Data.Array as Array
import Data.Lens (view)
import Data.Maybe (Maybe(..))
import Data.Newtype (wrap)
import Halogen.HTML (HTML, h2_, text)
import Types (_getPubKeyHash, _propertyName)
import Plutus.SCB.Webserver.Types (ChainReport(..))
import Prelude ((<<<), (==))

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
  namingFn pubKeyHash =
    Array.findMap
      ( \property ->
          let
            subject = view (propertySubject <<< _Subject) property

            hash = view _getPubKeyHash pubKeyHash
          in
            if subject == hash then
              view _propertyName property
            else
              Nothing
      )
      relatedMetadata
