{-# OPTIONS_GHC -Wwarn=unrecognised-pragmas #-}

module PlutusTx.Function (fix) where

fix :: forall a b. ((a -> b) -> a -> b) -> a -> b
fix f = let ~x = f x in x
{-# OPAQUE fix #-}
