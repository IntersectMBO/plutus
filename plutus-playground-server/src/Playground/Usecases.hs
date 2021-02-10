{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Playground.Usecases where

import           Data.ByteString              (ByteString)
import           Data.FileEmbed               (embedFile, makeRelativeToProject)
import qualified Data.Text                    as T
import qualified Data.Text.Encoding           as T
import           Language.Haskell.Interpreter (SourceCode (SourceCode))

marker :: T.Text
marker = "TRIM TO HERE\n"

strip :: T.Text -> T.Text
strip text = snd $ T.breakOnEnd marker text

process :: ByteString -> SourceCode
process = SourceCode . strip . T.decodeUtf8

vesting :: SourceCode
vesting = process $(makeRelativeToProject "usecases/Vesting.hs" >>= embedFile)

game :: SourceCode
game = process $(makeRelativeToProject "usecases/Game.hs" >>= embedFile)

errorHandling :: SourceCode
errorHandling =
    process $(makeRelativeToProject "usecases/ErrorHandling.hs" >>= embedFile)

crowdFunding :: SourceCode
crowdFunding =
    process $(makeRelativeToProject "usecases/Crowdfunding.hs" >>= embedFile)

starter :: SourceCode
starter = process $(makeRelativeToProject "usecases/Starter.hs" >>= embedFile)

helloWorld :: SourceCode
helloWorld = process $(makeRelativeToProject "usecases/HelloWorld.hs" >>= embedFile)
