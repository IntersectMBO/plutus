{-# LANGUAGE MagicHash, NegativeLiterals, BangPatterns,
             ForeignFunctionInterface, JavaScriptFFI, UnliftedFFITypes
  #-}

module Data.JSString.Internal where
{-
import           Prelude ( Eq(..), Ord(..), Show(..), Read(..), Bool(..)
                         , seq, Ordering(..))
import           Data.Data (Data(..))
import           Data.Monoid (Monoid(..))
import           Control.DeepSeq (NFData(..))
import qualified GHC.Exts as Exts

import           Unsafe.Coerce
import           GHCJS.Prim (JSVal)

newtype JSString = JSString (JSVal ())

instance Monoid JSString where
  mempty  = empty
  mappend = append
  mconcat = concat

instance Eq JSString where
  (==) = eqJSString

instance Ord JSString where
  compare = compareJSString

instance NFData JSString where rnf !_ = ()

compareJSString :: JSString -> JSString -> Ordering
compareJSString x y = Exts.tagToEnum# (js_compare x y Exts.+# 2#)
{-# INLINE compareJSString #-}

eqJSString :: JSString -> JSString -> Bool
eqJSString x y = js_eq
{-# INLINE eqJSString #-}

-- | /O(n)/ Appends one 'JSString' to the other by copying both of them
-- into a new 'JSString'.  Subject to fusion.
append :: JSString -> JSString -> JSString
append x y = js_append x y
{-# INLINE append #-}

{-# RULES
"JSSTRING append -> fused" [~1] forall t1 t2.
    append t1 t2 = unstream (S.append (stream t1) (stream t2))
"JSSTRING append -> unfused" [1] forall t1 t2.
    unstream (S.append (stream t1) (stream t2)) = append t1 t2
 #-}

-- | /O(n)/ Concatenate a list of 'JSString's.
concat :: [JSString] -> JSString
concat ts = rnf ts `seq` js_concat (unsafeCoerce ts)
{-# INLINE concat #-}

empty :: JSString
empty = js_empty
{-# INLINE empty #-}

-- -----------------------------------------------------------------------------

foreign import javascript unsafe
  "$r='';" js_empty :: JSString
foreign import javascript unsafe
  "$1+$2" js_append :: JSString -> JSString -> JSString
foreign import javascript unsafe
  "$1===$2" js_eq :: JSString -> JSString -> Bool
foreign import javascript unsafe
  "$1.localeCompare($2)" js_compare :: JSString -> JSString -> Exts.Int#
foreign import javascript unsafe
  "h$jsstringConcat" js_concat :: Exts.Any -> JSString
-}
