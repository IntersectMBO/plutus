-- |
-- Module      : Foundation.System.Entropy.Common
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
-- Common part for vectors
--
{-# LANGUAGE DeriveDataTypeable #-}
module Foundation.System.Entropy.Common
    ( EntropySystemMissing(..)
    ) where

import Basement.Compat.Base

data EntropySystemMissing = EntropySystemMissing
    deriving (Show,Eq,Typeable)

instance Exception EntropySystemMissing
