module Debug.Trace.Dump
    ( traceFile
    , traceFileBSL
    , traceFileText
    ) where

import qualified Data.ByteString.Lazy as BSL
import           Data.Functor
import qualified Data.Text            as T
import qualified Data.Text.IO         as TIO
import           System.IO.Unsafe     (unsafePerformIO)

traceFileBSL :: FilePath -> BSL.ByteString -> a -> a
traceFileBSL fp bytes x = unsafePerformIO $
    BSL.writeFile fp bytes $> x

traceFileText :: FilePath -> T.Text -> a -> a
traceFileText fp txt x = unsafePerformIO $
    TIO.writeFile fp txt $> x

traceFile :: FilePath -> String -> a -> a
traceFile fp str x = unsafePerformIO $
    writeFile fp str $> x
