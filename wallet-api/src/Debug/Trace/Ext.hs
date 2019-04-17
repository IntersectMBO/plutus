module Debug.Trace.Ext ( traceFile ) where

import           Data.Functor     (($>))
import           System.IO.Unsafe (unsafePerformIO)

traceFile :: FilePath -> String -> a -> a
traceFile fp contents x = unsafePerformIO $ writeFile fp contents $> x
