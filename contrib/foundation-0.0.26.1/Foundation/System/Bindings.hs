{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE CPP #-}
module Foundation.System.Bindings
    ( module X
    ) where

#ifdef mingw32_HOST_OS
import Foundation.System.Bindings.Windows as X
#else
import Foundation.System.Bindings.Posix as X
#endif
