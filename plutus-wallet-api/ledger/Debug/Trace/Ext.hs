module Debug.Trace.Ext ( traceFile
                       , traceFileBSL
                       ) where

import qualified Data.ByteString.Lazy as BSL
import           Data.Functor         (($>))
import           System.IO.Unsafe     (unsafePerformIO)

traceFile :: FilePath -> String -> a -> a
traceFile fp contents x = unsafePerformIO $ writeFile fp contents $> x

traceFileBSL :: FilePath -> BSL.ByteString -> a -> a
traceFileBSL fp contents x = unsafePerformIO $ BSL.writeFile fp contents $> x
