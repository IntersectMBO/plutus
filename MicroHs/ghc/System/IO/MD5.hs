-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module System.IO.MD5(MD5CheckSum, md5File, md5Handle) where
import Control.DeepSeq
import System.IO

newtype MD5CheckSum = MD5 [Word]  -- actually returns 16 bytes
  deriving (Eq, Show)

instance NFData MD5CheckSum where
  rnf (MD5 ws) = rnf ws

md5File :: FilePath -> IO (Maybe MD5CheckSum)
md5File _ = return (Just $ MD5 [])          -- dummy MD5

md5Handle :: Handle -> IO MD5CheckSum
md5Handle _ = return $ MD5 []          -- dummy MD5
