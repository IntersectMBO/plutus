{-# LANGUAGE TemplateHaskell #-}

module Meadow.Contracts where

import           Data.ByteString (ByteString)
import           Data.FileEmbed  (embedFile, makeRelativeToProject)

basicContract :: ByteString
basicContract = $(makeRelativeToProject "contracts/BasicContract.hs" >>= embedFile)
