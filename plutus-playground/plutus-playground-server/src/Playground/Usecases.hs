{-# LANGUAGE TemplateHaskell #-}

module Playground.Usecases where

import           Data.ByteString (ByteString)
import           Data.FileEmbed  (embedFile)

vesting :: ByteString
vesting = $(embedFile "./usecases/Vesting.hs")

game :: ByteString
game = $(embedFile "./usecases/Game.hs")

messages :: ByteString
messages = $(embedFile "./usecases/Messages.hs")

crowdfunding :: ByteString
crowdfunding = $(embedFile "./usecases/Crowdfunding.hs")
