module PlutusTx.Maybe (Maybe (..), isJust, isNothing, maybe, fromMaybe, mapMaybe) where

{-
We export off-chain Haskell's Maybe type as on-chain Plutus's Maybe type since they are the same.
-}

import PlutusTx.Base (id)
import PlutusTx.Bool
import PlutusTx.List (foldr)
import Prelude (Maybe (..))

{- HLINT ignore -}

{-| Check if a 'Maybe' @a@ is @Just a@

  >>> isJust Nothing
  False
  >>> isJust (Just "plutus")
  True -}
isJust :: Maybe a -> Bool
isJust m = case m of Just _ -> True; _ -> False
{-# INLINEABLE isJust #-}

{-| Check if a 'Maybe' @a@ is @Nothing@

  >>> isNothing Nothing
  True
  >>> isNothing (Just "plutus")
  False -}
isNothing :: Maybe a -> Bool
isNothing m = case m of Just _ -> False; _ -> True
{-# INLINEABLE isNothing #-}

{-| Plutus Tx version of 'Prelude.maybe'.

  >>> maybe "platypus" (\s -> s) (Just "plutus")
  "plutus"
  >>> maybe "platypus" (\s -> s) Nothing
  "platypus" -}
maybe :: b -> (a -> b) -> Maybe a -> b
maybe b f m = case m of
  Nothing -> b
  Just a -> f a
{-# INLINEABLE maybe #-}

-- | Plutus Tx version of 'Data.Maybe.fromMaybe'
fromMaybe :: a -> Maybe a -> a
fromMaybe a = maybe a id
{-# INLINEABLE fromMaybe #-}

{-| Plutus Tx version of 'Data.Maybe.mapMaybe'.

  >>> mapMaybe (\i -> if i == 2 then Just '2' else Nothing) [1, 2, 3, 4]
  "2" -}
mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe p = foldr (\e xs -> maybe xs (: xs) (p e)) []
{-# INLINEABLE mapMaybe #-}
