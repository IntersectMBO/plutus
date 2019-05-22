{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Git where

import           Data.FileEmbed     (dummySpaceWith)
import           Data.String        (fromString)
import           Data.Text          (Text)
import qualified Data.Text          as T
import           Data.Text.Encoding (decodeUtf8)
import           Git.TH             (gitRevFromGit)

-- | Try to get the git revision from the possibly injected gitRevEmbed
--   If it hasn't been embeded then try to get from the current compilation
--   environment. This allows us to get the revision for both Hydra and
--   local stack workflows
gitRev :: Text
gitRev | gitRevEmbed /= zeroRev = gitRevEmbed
       | T.null fromGit         = zeroRev
       | otherwise              = fromGit
    where
        -- Git revision embedded after compilation using
        -- Data.FileEmbed.injectWith. If nothing has been injected,
        -- this will be filled with 0 characters.
        gitRevEmbed :: Text
        gitRevEmbed = decodeUtf8 $(dummySpaceWith "gitrev" 40)

        -- Git revision found during compilation by running git. If
        -- git could not be run, then this will be empty.
        fromGit = T.strip (fromString $(gitRevFromGit))

zeroRev :: Text
zeroRev = "0000000000000000000000000000000000000000"
