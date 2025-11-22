module PlutusTx.Bool (Bool (..), (&&), (||), not, otherwise) where

{-
We export off-chain Haskell's Bool type as on-chain Plutus's Bool type since they are the same.
-}

import Prelude (Bool (..), otherwise)

{- HLINT ignore -}

-- `(&&)` and `(||)` are handled specially in the plugin to make sure they can short-circuit.
-- See Note [Lazy boolean operators] in the plugin.
-- In the Haskell-side, we are using `default-extensions: Strict` throughout PlutusTx,
-- which means that we have to sure that the second argument is lazy to short-circuit the `(&&)` and `(||)`.

{-| Logical AND. Short-circuits if the first argument evaluates to `False`.

  >>> True && False
  False

  >>> False && error ()
  False
-}
infixr 3 &&

(&&) :: Bool -> Bool -> Bool
(&&) l ~r = if l then r else False
{-# OPAQUE (&&) #-}

{-| Logical OR. Short-circuits if the first argument evaluates to `True`.

  >>> True || False
  True

  >>> True || error ()
  True
-}
infixr 2 ||

(||) :: Bool -> Bool -> Bool
(||) l ~r = if l then True else r
{-# OPAQUE (||) #-}

{-| Logical negation

  >>> not True
  False
-}
not :: Bool -> Bool
not a = if a then False else True
{-# INLINEABLE not #-}
