{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Bool ((&&), (||), not) where

import           Prelude hiding (not, (&&), (||))

{-# ANN module ("HLint: ignore"::String) #-}

{-# NOINLINE (&&) #-}
-- | Logical AND
--
--   >>> True && False
--   False
--
infixr 3 &&
(&&) :: Bool -> Bool -> Bool
(&&) l r = if l then r else False

{-# NOINLINE (||) #-}
-- | Logical OR
--
--   >>> True || False
--   True
--
infixr 2 ||
(||) :: Bool -> Bool -> Bool
(||) l r = if l then True else r

{-# NOINLINE not #-}
-- | Logical negation
--
--   >>> not True
--   False
--
not :: Bool -> Bool
not a = if a then False else True
