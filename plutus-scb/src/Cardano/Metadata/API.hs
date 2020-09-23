{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

module Cardano.Metadata.API
    ( API
    ) where

import           Cardano.Metadata.Types (JSONEncoding, PropertyDescription, PropertyKey, Subject, SubjectProperties)
import           Servant.API            ((:<|>), (:>), Capture, Get, JSON)

type API (encoding :: JSONEncoding)
     = "metadata" :> Capture "subject" Subject :> ("properties" :> Get '[ JSON] (Maybe (SubjectProperties encoding))
                                                   :<|> "property" :> Capture "property" PropertyKey :> Get '[ JSON] (Maybe (PropertyDescription encoding)))
