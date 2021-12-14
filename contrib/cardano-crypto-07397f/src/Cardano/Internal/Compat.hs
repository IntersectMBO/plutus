{-# LANGUAGE CPP #-}
module Cardano.Internal.Compat (fromRight) where
#if MIN_VERSION_base(4, 10, 0)
import Data.Either(fromRight)
#endif

#if !MIN_VERSION_base(4, 10, 0)
fromRight :: b -> Either a b -> b
fromRight _ (Right b) = b
fromRight b _         = b
#endif
