{-# LANGUAGE TemplateHaskell #-}

module Playground.Usecases where

import           Data.ByteString (ByteString)
import           Data.FileEmbed  (embedFile, makeRelativeToProject)

vesting :: ByteString
vesting = $(makeRelativeToProject "usecases/Vesting.hs" >>= embedFile)

game :: ByteString
game = $(makeRelativeToProject "usecases/Game.hs" >>= embedFile)

messages :: ByteString
messages = $(makeRelativeToProject "usecases/Messages.hs" >>= embedFile)

crowdfunding :: ByteString
crowdfunding = $(makeRelativeToProject "usecases/CrowdFunding.hs" >>= embedFile)
