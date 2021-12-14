-- |
-- Module      : Foundation.Class.Bifunctor
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
-- Formally, the class 'Bifunctor' represents a bifunctor
-- from @Hask@ -> @Hask@.
--
-- Intuitively it is a bifunctor where both the first and second
-- arguments are covariant.
--
-- You can define a 'Bifunctor' by either defining 'bimap' or by
-- defining both 'first' and 'second'.
--
{-# LANGUAGE CPP #-}
module Foundation.Class.Bifunctor
  ( module Basement.Compat.Bifunctor
  ) where

import Basement.Compat.Bifunctor
