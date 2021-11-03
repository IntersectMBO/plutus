{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Bool (Bool(..), (&&), (||), not, otherwise) where

{-
We export off-chain Haskell's Bool type as on-chain Plutus's Bool type since they are the same.
-}

import Prelude (Bool (..), otherwise)

{- HLINT ignore -}

{-# INLINABLE (&&) #-}
-- | Logical AND
--
--   >>> True && False
--   False
--
infixr 3 &&
(&&) :: Bool -> Bool -> Bool
(&&) l r = if l then r else False

{-# INLINABLE (||) #-}
-- | Logical OR
--
--   >>> True || False
--   True
--
infixr 2 ||
(||) :: Bool -> Bool -> Bool
(||) l r = if l then True else r

{-# INLINABLE not #-}
-- | Logical negation
--
--   >>> not True
--   False
--
not :: Bool -> Bool
not a = if a then False else True
