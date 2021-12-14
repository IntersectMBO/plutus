-- |
-- Module      : Foundation.Random
-- License     : BSD-style
-- Stability   : experimental
-- Portability : Good
--
-- This module deals with the random subsystem abstractions.
--
-- It provide 2 different set of abstractions:
--
-- * The first abstraction that allow a monad to generate random
--   through the 'MonadRandom' class.
--
-- * The second abstraction to make generic random generator 'RandomGen'
--   and a small State monad like wrapper 'MonadRandomState' to
--   abstract a generator.
--
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ScopedTypeVariables      #-}
module Foundation.Random
    ( MonadRandom(..)
    , RandomGen(..)
    , MonadRandomState(..)
    , withRandomGenerator
    , RNG
    , RNGv1
    ) where

import           Foundation.Random.Class
import           Foundation.Random.DRG
import qualified Foundation.Random.ChaChaDRG as ChaChaDRG

-- | An alias to the default choice of deterministic random number generator
--
-- Unless, you want to have the stability of a specific random number generator,
-- e.g. for tests purpose, it's recommended to use this alias so that you would
-- keep up to date with possible bugfixes, or change of algorithms.
type RNG = RNGv1

type RNGv1 = ChaChaDRG.State
