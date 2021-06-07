{-# LANGUAGE BangPatterns #-}
module Tests.SlowFunctions
    (
      indices
    , splitOn
    ) where

import qualified Data.JSString as J

indices :: J.JSString          -- ^ Substring to search for (@needle@)
        -> J.JSString          -- ^ Text to search in (@haystack@)
        -> [Int]
indices needle haystack
    | J.null needle = []
    | otherwise     = scan 0
  where
    hlen = J.length haystack
    nlen = J.length needle
    scan i | i >= hlen = []
           | needle `J.isPrefixOf` (J.drop i haystack) = i : scan (i+nlen) -- slow!
           | otherwise                                 = scan (i+1)
--           where t = J.drop i h -- Text harr (hoff+i) (hlen-i)
--                 d = iter_ haystack i

splitOn :: J.JSString           -- ^ Text to split on
        -> J.JSString           -- ^ Input text
        -> [J.JSString]
splitOn pat src0
    | J.null pat  = error "SPLsplitOn: empty"
-- -    | l == 1      = J.split (== (J.head pat)) src0 -- (unsafeHead pat)) src0
    | otherwise   = go src0
  where
    l      = J.length pat
    go src = search 0 src
      where
        search !n !s
            | J.null s             = [src]      -- not found
            | pat `J.isPrefixOf` s = J.take n src : go (J.drop l s)
            | otherwise            = search (n+1) (J.tail s) -- unsafeTail s)
