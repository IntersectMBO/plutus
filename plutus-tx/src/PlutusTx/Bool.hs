module PlutusTx.Bool (Bool(..), (&&), (||), not, otherwise) where

{-
We export off-chain Haskell's Bool type as on-chain Plutus's Bool type since they are the same.
-}

import Prelude (Bool (..), otherwise)

{- HLINT ignore -}

-- `(&&)` and `(||)` are handled specially in the plugin to make sure they can short-circuit.
-- See Note [Lazy boolean operators] in the plugin.

{-# OPAQUE (&&) #-}
-- | Logical AND. Short-circuits if the first argument evaluates to `False`.
--
--   >>> True && False
--   False
--
infixr 3 &&
(&&) :: Bool -> Bool -> Bool
(&&) l r = if l then r else False

{-# OPAQUE (||) #-}
-- | Logical OR. Short-circuits if the first argument evaluates to `True`.
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
