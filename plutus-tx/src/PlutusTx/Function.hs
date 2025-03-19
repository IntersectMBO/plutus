{-# LANGUAGE CPP #-}
#if !MIN_VERSION_base(4, 15, 0)
{-# OPTIONS_GHC -Wwarn=unrecognised-pragmas #-}
#endif

module PlutusTx.Function (fix) where

fix :: forall a b. ((a -> b) -> a -> b) -> a -> b
fix f = let ~x = f x in x
{-# OPAQUE fix #-}
