{-# LANGUAGE TypeOperators #-}

module Servant.Extra where

import           Servant ((:<|>) ((:<|>)))

left ::
       (a
        :<|> b)
    -> a
left x =
    let (a :<|> _) = x
     in a

right ::
       (a
        :<|> b)
    -> b
right x =
    let (_ :<|> b) = x
     in b
