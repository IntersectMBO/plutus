{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE LambdaCase             #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Ledger.These.TH(
    These(..)
  , these
  , theseWithDefault
  ) where

import           Language.Haskell.TH          (Q, TExp)

-- | A 'These' @a@ @b@ is either an @a@, or a @b@ or an @a@ and a @b@.
-- Plutus version of 'Data.These'.
data These a b = This a | That b | These a b

-- | Consume a 'These a b' value.
theseWithDefault :: Q (TExp (a -> b -> (a -> b -> c) -> These a b -> c))
theseWithDefault = [|| 

    let theseWithDefault :: forall a b c. a -> b -> (a -> b -> c) -> These a b -> c
        theseWithDefault a' b' f = \case 
            This a -> f a b'
            That b -> f a' b
            These a b -> f a b
    in theseWithDefault

    ||]

these :: Q (TExp ((a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c))
these = [||
    \f g h -> \case
        This a -> f a
        That b -> g b
        These a b -> h a b
    ||]
