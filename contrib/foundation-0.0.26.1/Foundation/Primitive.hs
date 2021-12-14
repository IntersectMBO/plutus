-- |
-- Module      : Foundation.Primitive
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
--
{-# LANGUAGE FlexibleInstances #-}
module Foundation.Primitive
    ( PrimType(..)
    , PrimMonad(..)

    -- * endianess
    , ByteSwap
    , LE(..), toLE, fromLE
    , BE(..), toBE, fromBE

    -- * Integral convertion
    , IntegralUpsize(..)
    , IntegralDownsize(..)

    -- * Evaluation
    , NormalForm(..)
    , force
    , deepseq

    -- * These
    , These(..)

    -- * Block of memory
    , Block
    , MutableBlock

    -- * Ascii
    , Char7
    , AsciiString
    ) where

import Basement.PrimType
import Basement.Types.Char7
import Basement.Types.AsciiString
import Basement.Monad
import Basement.Endianness
import Basement.IntegralConv
import Basement.NormalForm
import Basement.These
import Basement.Block
