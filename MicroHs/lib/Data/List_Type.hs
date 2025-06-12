module Data.List_Type(module Data.List_Type) where
import Prelude qualified ()
import Primitives

infixr 5 :
data [] a = [] | (:) a [a]  -- Parser hacks makes this acceptable

-- This does not really belong here, but it makes the module structure
-- much simpler.
infixr 5 ++
(++) :: forall a . [a] -> [a] -> [a]
axs ++ ys =
  let go []     = ys
      go (x:xs) = x : go xs
  in  go axs

-- Put concatMap here so list comprehensions can be desugared
-- using only List_Type
concatMap :: forall a b . (a -> [b]) -> [a] -> [b]
concatMap _ []       = []
concatMap f (x : xs) = f x ++ concatMap f xs
