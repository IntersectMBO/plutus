{-# LANGUAGE TemplateHaskell #-}

module Meadow.Contracts where

import           Data.ByteString (ByteString)
import           Data.FileEmbed  (embedFile, makeRelativeToProject)

escrow :: ByteString
escrow = $(makeRelativeToProject "contracts/Escrow.hs" >>= embedFile)

zeroCouponBond :: ByteString
zeroCouponBond = $(makeRelativeToProject "contracts/ZeroCouponBond.hs" >>= embedFile)

couponBondGuaranteed :: ByteString
couponBondGuaranteed = $(makeRelativeToProject "contracts/CouponBondGuaranteed.hs" >>= embedFile)

