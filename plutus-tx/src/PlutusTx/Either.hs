{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusTx.Either (Either (..), isLeft, isRight, either) where

{-
We export off-chain Haskell's Either type as on-chain Plutus's Either type since they are the same.
-}

import PlutusTx.Bool (Bool (..))
import Prelude (Either (..))

{- HLINT ignore -}

-- | Return `True` if the given value is a `Left`-value, `False` otherwise.
isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False
{-# INLINEABLE isLeft #-}

-- | Return `True` if the given value is a `Right`-value, `False` otherwise.
isRight :: Either a b -> Bool
isRight (Left _) = False
isRight (Right _) = True
{-# INLINEABLE isRight #-}

-- | Plutus Tx version of 'Prelude.either'
either :: (a -> c) -> (b -> c) -> Either a b -> c
either f _ (Left x) = f x
either _ g (Right y) = g y
{-# INLINEABLE either #-}
