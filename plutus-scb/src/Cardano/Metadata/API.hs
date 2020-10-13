{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

module Cardano.Metadata.API
    ( API
    ) where

import           Cardano.Metadata.Types (JSONEncoding, Property, PropertyKey, Query, Subject, SubjectProperties)
import           Servant.API            ((:<|>), (:>), Capture, Get, JSON, ReqBody)

type API (encoding :: JSONEncoding)
     = "metadata" :> (Capture "subject" Subject :> ("properties" :> Get '[ JSON] (SubjectProperties encoding)
                                                    :<|> "property" :> Capture "property" PropertyKey :> Get '[ JSON] (Property encoding))
                      :<|> "query" :> ReqBody '[ JSON] Query :> Get '[ JSON] [SubjectProperties encoding])
