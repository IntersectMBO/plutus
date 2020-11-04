{-# LANGUAGE TemplateHaskell #-}

module Marlowe.Contracts where

import           Data.ByteString (ByteString)
import           Data.FileEmbed  (embedFile, makeRelativeToProject)

example :: ByteString
example = $(makeRelativeToProject "contracts/Example.hs" >>= embedFile)

escrow :: ByteString
escrow = $(makeRelativeToProject "contracts/Escrow.hs" >>= embedFile)

zeroCouponBond :: ByteString
zeroCouponBond = $(makeRelativeToProject "contracts/ZeroCouponBond.hs" >>= embedFile)

couponBondGuaranteed :: ByteString
couponBondGuaranteed = $(makeRelativeToProject "contracts/CouponBondGuaranteed.hs" >>= embedFile)

swap :: ByteString
swap = $(makeRelativeToProject "contracts/Swap.hs" >>= embedFile)

option :: ByteString
option = $(makeRelativeToProject "contracts/Option.hs" >>= embedFile)

contractForDifference :: ByteString
contractForDifference = $(makeRelativeToProject "contracts/ContractForDifference.hs" >>= embedFile)
