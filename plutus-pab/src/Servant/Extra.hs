{-# LANGUAGE TypeOperators #-}

module Servant.Extra
    ( capture
    , left
    , right
    ) where

import           Data.Bifunctor (bimap)
import           Servant        ((:<|>) ((:<|>)))

capture ::
       ((a -> b)
        :<|> (a -> c))
    -> a
    -> (b
        :<|> c)
capture handlers arg = bimap ($ arg) ($ arg) handlers

left ::
       (a
        :<|> b)
    -> a
left x = l
  where
    (l :<|> _) = x

right ::
       (a
        :<|> b)
    -> b
right x = r
  where
    (_ :<|> r) = x
