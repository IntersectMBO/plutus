module Data.Text.Lazy.IO(readFile, writeFile, hPutStr) where
import Prelude hiding (readFile, writeFile)
import qualified Prelude as P
import Data.Text.Lazy
import qualified System.IO as IO

readFile :: FilePath -> IO Text
readFile fn = pack <$> P.readFile fn

writeFile :: FilePath -> Text -> IO ()
writeFile fn t = P.writeFile fn (unpack t)

hPutStr :: IO.Handle -> Text -> IO ()
hPutStr h t = IO.hPutStr h (unpack t)
