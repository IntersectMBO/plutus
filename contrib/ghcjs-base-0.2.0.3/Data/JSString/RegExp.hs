{-# LANGUAGE JavaScriptFFI #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MagicHash #-}

module Data.JSString.RegExp ( RegExp
                            , pattern
                            , isMultiline
                            , isIgnoreCase
                            , Match(..)
                            , REFlags(..)
                            , create
                            , test
                            , exec
                            , execNext
                            ) where

import GHCJS.Prim
import GHC.Exts (Any, Int#, Int(..))

import Unsafe.Coerce (unsafeCoerce)

import Data.JSString
import Data.Typeable

newtype RegExp = RegExp JSVal deriving Typeable

data REFlags = REFlags { multiline  :: !Bool
                       , ignoreCase :: !Bool
                       }

data Match = Match { matched       :: !JSString  -- ^ the matched string
                   , subMatched    :: [JSString] -- ^ the matched parentesized substrings
                   , matchRawIndex :: !Int       -- ^ the raw index of the match in the string
                   , matchInput    :: !JSString  -- ^ the input string
                   }

create :: REFlags -> JSString -> RegExp
create flags pat = js_createRE pat flags'
  where
    flags' | multiline flags = if ignoreCase flags then "mi" else "m"
           | otherwise       = if ignoreCase flags then "i"  else ""
{-# INLINE create #-}

pattern :: RegExp -> JSString
pattern re = js_pattern re

isMultiline :: RegExp -> Bool
isMultiline re = js_isMultiline re

isIgnoreCase :: RegExp -> Bool
isIgnoreCase re = js_isIgnoreCase re

test :: JSString -> RegExp -> Bool
test x re = js_test x re
{-# INLINE test #-}

exec :: JSString -> RegExp -> Maybe Match
exec x re = exec' 0# x re
{-# INLINE exec #-}

execNext :: Match -> RegExp -> Maybe Match
execNext m re = case matchRawIndex m of
                  I# i -> exec' i (matchInput m) re
{-# INLINE execNext #-}

exec' :: Int# -> JSString -> RegExp -> Maybe Match
exec' i x re = case js_exec i x re of
                 (# -1#, _, _ #) -> Nothing
                 (# i',  y, z #) -> Just (Match y (unsafeCoerce z) (I# i) x)
{-# INLINE exec' #-}

matches :: JSString -> RegExp -> [Match]
matches x r = maybe [] go (exec x r)
  where
    go m = m : maybe [] go (execNext m r)
{-# INLINE matches #-}

replace :: RegExp -> JSString -> JSString -> JSString
replace x r = error "Data.JSString.RegExp.replace not implemented"
{-# INLINE replace #-}

split :: JSString -> RegExp -> [JSString]
split x r = unsafeCoerce (js_split -1# x r)
{-# INLINE split #-}

splitN :: Int -> JSString -> RegExp -> [JSString]
splitN (I# k) x r = unsafeCoerce (js_split k x r)
{-# INLINE splitN #-}

-- ----------------------------------------------------------------------------

foreign import javascript unsafe
  "new RegExp($1,$2)" js_createRE :: JSString -> JSString -> RegExp
foreign import javascript unsafe
  "$2.test($1)" js_test :: JSString -> RegExp -> Bool
foreign import javascript unsafe
  "h$jsstringExecRE" js_exec
  :: Int# -> JSString -> RegExp -> (# Int#, JSString, Any {- [JSString] -} #)
foreign import javascript unsafe
  "h$jsstringReplaceRE" js_replace :: RegExp -> JSString -> JSString -> JSString
foreign import javascript unsafe
  "h$jsstringSplitRE" js_split :: Int# -> JSString -> RegExp -> Any -- [JSString]
foreign import javascript unsafe
  "$1.multiline" js_isMultiline :: RegExp -> Bool
foreign import javascript unsafe
  "$1.ignoreCase" js_isIgnoreCase :: RegExp -> Bool
foreign import javascript unsafe
  "$1.pattern" js_pattern :: RegExp -> JSString

