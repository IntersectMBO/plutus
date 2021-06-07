{-# LANGUAGE MagicHash, BangPatterns, UnboxedTuples, TypeFamilies,
             ForeignFunctionInterface, JavaScriptFFI, UnliftedFFITypes,
             GHCForeignImportPrim, CPP
  #-}
{-| Manipulation of JavaScript strings, API and fusion implementation
    based on Data.Text by Tom Harper, Duncan Coutts, Bryan O'Sullivan e.a.
 -}
module Data.JSString ( JSString

                       -- * Creation and elimination
                     , pack
                     , unpack, unpack'
                     , singleton
                     , empty

                       -- * Basic interface
                     , cons
                     , snoc
                     , append
                     , uncons
                     , unsnoc
                     , head
                     , last
                     , tail
                     , init
                     , null
                     , length
                     , compareLength

                       -- * Transformations
                     , map
                     , intercalate
                     , intersperse
                     , transpose
                     , reverse
                     , replace

                       -- ** Case conversion
                     , toCaseFold
                     , toLower
                     , toUpper
                     , toTitle

                       -- ** Justification
                     , justifyLeft
                     , justifyRight
                     , center

                       -- * Folds
                     , foldl
                     , foldl'
                     , foldl1
                     , foldl1'
                     , foldr
                     , foldr1

                       -- ** Special folds
                     , concat
                     , concatMap
                     , any
                     , all
                     , maximum
                     , minimum

                       -- * Construction

                       -- ** Scans
                     , scanl
                     , scanl1
                     , scanr
                     , scanr1

                       -- ** Accumulating maps
                     , mapAccumL
                     , mapAccumR

                       -- ** Generation and unfolding
                     , replicate
                     , unfoldr
                     , unfoldrN

                       -- * Substrings

                       -- ** Breaking strings
                     , take
                     , takeEnd
                     , drop
                     , dropEnd
                     , takeWhile
                     , takeWhileEnd
                     , dropWhile
                     , dropWhileEnd
                     , dropAround
                     , strip
                     , stripStart
                     , stripEnd
                     , splitAt
                     , breakOn
                     , breakOnEnd
                     , break
                     , span
                     , group
                     , group'
                     , groupBy
                     , inits
                     , tails

                       -- ** Breaking into many substrings
                     , splitOn, splitOn'
                     , split
                     , chunksOf, chunksOf'

                       -- ** Breaking into lines and words
                     , lines, lines'
                     , words, words'
                     , unlines
                     , unwords

                       -- * Predicates
                     , isPrefixOf
                     , isSuffixOf
                     , isInfixOf

                       -- ** View patterns
                     , stripPrefix
                     , stripSuffix
                     , commonPrefixes

                       -- * Searching
                     , filter
                     , breakOnAll, breakOnAll'
                     , find
                     , partition

                       -- * Indexing
                     , index
                     , findIndex
                     , count

                       -- * Zipping
                     , zip
                     , zipWith
                     ) where

import           Prelude
  ( Char, Bool(..), Int, Maybe(..), String, Eq(..), Ord(..), Ordering(..), (++)
  , Read(..), Show(..), (&&), (||), (+), (-), (.), ($), ($!), (>>)
  , not, seq, return, otherwise, quot)
import qualified Prelude                              as P

import           Control.DeepSeq                      (NFData(..))
import           Data.Binary                          (Binary(..))
import           Data.Char                            (isSpace)
import qualified Data.List                            as L
import           Data.Data

import           GHC.Exts
  ( Int#, (+#), (-#), (>=#), (>#), isTrue#, chr#, Char(..)
  , Int(..), Addr#, tagToEnum#)
import qualified GHC.Exts                             as Exts
import qualified GHC.CString                          as GHC
import qualified GHC.Base                             as GHC

#if MIN_VERSION_base(4,9,0)
import Data.Semigroup (Semigroup(..))
#endif

import           Unsafe.Coerce

import           GHCJS.Prim                           (JSVal)
import qualified GHCJS.Prim                           as Prim

import           Data.JSString.Internal.Type
import           Data.JSString.Internal.Fusion        (stream, unstream)
import qualified Data.JSString.Internal.Fusion        as S
import qualified Data.JSString.Internal.Fusion.Common as S

import           Text.Printf                          (PrintfArg(..), formatString)

getJSVal :: JSString -> JSVal
getJSVal (JSString x) = x
{-# INLINE getJSVal #-}

instance Exts.IsString JSString where
  fromString = pack

instance Exts.IsList JSString where
  type Item JSString = Char
  fromList           = pack
  toList             = unpack

#if MIN_VERSION_base(4,9,0)
instance Semigroup JSString where
  (<>) = append
#endif

instance P.Monoid JSString where
  mempty  = empty
#if MIN_VERSION_base(4,9,0)
  mappend = (<>) -- future-proof definition
#else
  mappend = append
#endif
  mconcat = concat

instance Eq JSString where
  x == y = js_eq x y

{-
instance Binary JSString where
  put jss = put (encodeUtf8 jss)
  get     = do
    bs <- get
    case decodeUtf8' bs of
      P.Left exn -> P.fail (P.show exn)
      P.Right a  -> P.pure a
-}

#if MIN_VERSION_base(4,7,0)
instance PrintfArg JSString where
  formatArg txt = formatString $ unpack txt
#endif

instance Ord JSString where
  compare x y = compareStrings x y

equals :: JSString -> JSString -> Bool
equals x y = js_eq x y
{-# INLINE equals #-}

compareStrings :: JSString -> JSString -> Ordering
compareStrings x y = tagToEnum# (js_compare x y +# 1#)
{-# INLINE compareStrings #-}

-- | This instance preserves data abstraction at the cost of inefficiency.
--   See Data.Text for more information
instance Data JSString where
  gfoldl f z txt = z pack `f` (unpack txt)
  toConstr _ = packConstr
  gunfold k z c = case constrIndex c of
    1 -> k (z pack)
    _ -> P.error "gunfold"
  dataTypeOf _ = jsstringDataType

packConstr :: Constr
packConstr = mkConstr jsstringDataType "pack" [] Prefix

jsstringDataType :: DataType
jsstringDataType = mkDataType "Data.JSString.JSString" [packConstr]

instance Show JSString where
  showsPrec p ps r = showsPrec p (unpack ps) r

instance Read JSString where
  readsPrec p str = [(pack x,y) | (x,y) <- readsPrec p str]

-- -----------------------------------------------------------------------------
-- * Conversion to/from 'JSString'

-- | /O(n)/ Convert a 'String' into a 'JSString'.  Subject to
-- fusion.
pack :: String -> JSString
pack x = rnf x `seq` js_pack (unsafeCoerce x)
{-# INLINE [1] pack #-}

{-# RULES
"JSSTRING pack -> fused" [~1] forall x.
    pack x = unstream (S.map safe (S.streamList x))
"JSSTRING pack -> unfused" [1] forall x.
    unstream (S.map safe (S.streamList x)) = pack x
  #-}

-- | /O(n)/ Convert a 'JSString' into a 'String'.  Subject to fusion.
unpack :: JSString -> String
unpack = S.unstreamList . stream
{-# INLINE [1] unpack #-}

unpack' :: JSString -> String
unpack' x = unsafeCoerce (js_unpack x)
{-# INLINE unpack' #-}

-- | /O(n)/ Convert a literal string into a JSString.  Subject to fusion.
unpackCString# :: Addr# -> JSString
unpackCString# addr# = unstream (S.streamCString# addr#)
{-# NOINLINE unpackCString# #-}

{-# RULES "JSSTRING literal" forall a.
    unstream (S.map safe (S.streamList (GHC.unpackCString# a)))
      = unpackCString# a #-}

{-# RULES "JSSTRING literal UTF8" forall a.
    unstream (S.map safe (S.streamList (GHC.unpackCStringUtf8# a)))
      = unpackCString# a #-}

{-# RULES "JSSTRING empty literal"
    unstream (S.map safe (S.streamList []))
      = empty_ #-}

{-# RULES "JSSTRING singleton literal" forall a.
    unstream (S.map safe (S.streamList [a]))
      = singleton a #-}

#if MIN_VERSION_ghcjs_prim(0,1,1)
{-# RULES "JSSTRING literal prim" [0] forall a.
    unpackCString# a = JSString (Prim.unsafeUnpackJSStringUtf8# a)
  #-}
#endif

-- | /O(1)/ Convert a character into a 'JSString'.  Subject to fusion.
-- Performs replacement on invalid scalar values.
singleton :: Char -> JSString
singleton c = js_singleton c -- unstream . S.singleton . safe
{-# INLINE [1] singleton #-}

{-# RULES
"JSSTRING singleton -> fused" [~1] forall a.
    singleton a = unstream (S.singleton (safe a))
"JSSTRING singleton -> unfused" [1] forall a.
    unstream (S.singleton (safe a)) = singleton a
 #-}

-- This is intended to reduce inlining bloat.
-- singleton_ :: Char -> Text
-- singleton_ c = js_singleton c

-- Text (A.run x) 0 len
--  where x :: ST s (A.MArray s)
--        x = do arr <- A.new len
--               _ <- unsafeWrite arr 0 d
--               return arr
--        len | d < '\x10000' = 1
-- x           | otherwise     = 2
--        d = safe c
-- {-# NOINLINE singleton_ #-}

-- -----------------------------------------------------------------------------
-- * Basic functions

-- | /O(n)/ Adds a character to the front of a 'JSString'.  This function
-- is more costly than its 'List' counterpart because it requires
-- copying a new array.  Subject to fusion.  Performs replacement on
-- invalid scalar values.
cons :: Char -> JSString -> JSString
cons c x = js_cons c x
{-# INLINE [1] cons #-}

{-# RULES
"JSSTRING cons -> fused" [~1] forall c x.
    cons c x = unstream (S.cons (safe c) (stream x))
"JSSTRING cons -> unfused" [1] forall c x.
    unstream (S.cons (safe c) (stream x)) = cons c x
 #-}

infixr 5 `cons`

-- | /O(n)/ Adds a character to the end of a 'JSString'.  This copies the
-- entire array in the process, unless fused.  Subject to fusion.
-- Performs replacement on invalid scalar values.
snoc :: JSString -> Char -> JSString
snoc x c = js_snoc x c
  -- unstream (S.snoc (stream t) (safe c))
{-# INLINE [1] snoc #-}

{-# RULES
"JSSTRING snoc -> fused" [~1] forall x c.
    snoc x c = unstream (S.snoc (stream x) (safe c))
"JSSTRING snoc -> unfused" [1] forall x c.
    unstream (S.snoc (stream x) (safe c)) = snoc x c
 #-}

-- | /O(n)/ Appends one 'JSString' to the other by copying both of them
-- into a new 'JSString'.  Subject to fusion.
append :: JSString -> JSString -> JSString
append x y = js_append x y
{-# INLINE [1] append #-}

{-# RULES
"JSSTRING append -> fused" [~1] forall x1 x2.
    append x1 x2 = unstream (S.append (stream x1) (stream x2))
"JSSTRING append -> unfused" [1] forall x1 x2.
    unstream (S.append (stream x1) (stream x2)) = append x1 x2
 #-}

-- | /O(1)/ Returns the first character of a 'JSString', which must be
-- non-empty.  Subject to fusion.
head :: JSString -> Char
head x = case js_head x of
                -1# -> emptyError "head"
                ch  -> C# (chr# ch)
{-# INLINE [1] head #-}

{-# RULES
"JSSTRING head -> fused" [~1] forall x.
    head x = S.head (stream x)
"JSSTRING head -> unfused" [1] forall x.
    S.head (stream x) = head x
 #-}


-- | /O(1)/ Returns the first character and rest of a 'JSString', or
-- 'Nothing' if empty. Subject to fusion.
uncons :: JSString -> Maybe (Char, JSString)
uncons x = case js_uncons x of
             (# -1#, _ #) -> Nothing
             (# cp, t  #) -> Just (C# (chr# cp), t)
{-# INLINE [1] uncons #-}

unsnoc :: JSString -> Maybe (JSString, Char)
unsnoc x = case js_unsnoc x of
             (# -1#, _ #) -> Nothing
             (# cp, t  #) -> Just (t, C# (chr# cp))
{-# INLINE [1] unsnoc #-}

-- | Lifted from Control.Arrow and specialized.
second :: (b -> c) -> (a,b) -> (a,c)
second f (a, b) = (a, f b)

-- | /O(1)/ Returns the last character of a 'JSString', which must be
-- non-empty.  Subject to fusion.
last :: JSString -> Char
last x = case js_last x of
           -1# -> emptyError "last"
           c   -> (C# (chr# c))
{-# INLINE [1] last #-}

{-# RULES
"JSSTRING last -> fused" [~1] forall x.
    last x = S.last (stream x)
"JSSTRING last -> unfused" [1] forall x.
    S.last (stream x) = last x
  #-}

-- | /O(1)/ Returns all characters after the head of a 'JSString', which
-- must be non-empty.  Subject to fusion.
tail :: JSString -> JSString
tail x =
  let r = js_tail x
  in  if js_isNull r
      then emptyError "tail"
      else JSString r
{-# INLINE [1] tail #-}

{-# RULES
"JSSTRING tail -> fused" [~1] forall x.
    tail x = unstream (S.tail (stream x))
"JSSTRING tail -> unfused" [1] forall x.
    unstream (S.tail (stream x)) = tail x
 #-}

-- | /O(1)/ Returns all but the last character of a 'JSString', which must
-- be non-empty.  Subject to fusion.
init :: JSString -> JSString
init x =
  let r = js_init x
  in  if js_isNull r
      then emptyError "init"
      else JSString r
{-# INLINE [1] init #-}

{-# RULES
"JSSTRING init -> fused" [~1] forall t.
    init t = unstream (S.init (stream t))
"JSSTRING init -> unfused" [1] forall t.
    unstream (S.init (stream t)) = init t
 #-}

-- | /O(1)/ Tests whether a 'JSString' is empty or not.  Subject to
-- fusion.
null :: JSString -> Bool
null x = js_null x
{-# INLINE [1] null #-}

{-# RULES
"JSSTRING null -> fused" [~1] forall t.
    null t = S.null (stream t)
"JSSTRING null -> unfused" [1] forall t.
    S.null (stream t) = null t
 #-}

-- | /O(1)/ Tests whether a 'JSString' contains exactly one character.
-- Subject to fusion.
isSingleton :: JSString -> Bool
isSingleton x = js_isSingleton x
{-# INLINE [1] isSingleton #-}

{-# RULES
"JSSTRING isSingleton -> fused" [~1] forall x.
    isSingleton x = S.isSingleton (stream x)
"JSSTRING isSingleton -> unfused" [1] forall x.
    S.isSingleton (stream x) = isSingleton x
 #-}

-- | /O(n)/ Returns the number of characters in a 'JSString'.
-- Subject to fusion.
length :: JSString -> Int
length x = S.length (stream x)
{-# INLINE [0] length #-}
-- length needs to be phased after the compareN/length rules otherwise
-- it may inline before the rules have an opportunity to fire.

-- | /O(n)/ Compare the count of characters in a 'JSString' to a number.
-- Subject to fusion.
--
-- This function gives the same answer as comparing against the result
-- of 'length', but can short circuit if the count of characters is
-- greater than the number, and hence be more efficient.
compareLength :: JSString -> Int -> Ordering
compareLength t n = S.compareLengthI (stream t) n
{-# INLINE [1] compareLength #-}

{-# RULES
"JSSTRING compareN/length -> compareLength" [~1] forall t n.
    compare (length t) n = compareLength t n
  #-}

{-# RULES
"JSSTRING ==N/length -> compareLength/==EQ" [~1] forall t n.
    GHC.eqInt (length t) n = compareLength t n == EQ
  #-}

{-# RULES
"JSSTRING /=N/length -> compareLength//=EQ" [~1] forall t n.
    GHC.neInt (length t) n = compareLength t n /= EQ
  #-}

{-# RULES
"JSSTRING <N/length -> compareLength/==LT" [~1] forall t n.
    GHC.ltInt (length t) n = compareLength t n == LT
  #-}

{-# RULES
"JSSTRING <=N/length -> compareLength//=GT" [~1] forall t n.
    GHC.leInt (length t) n = compareLength t n /= GT
  #-}

{-# RULES
"JSSTRING >N/length -> compareLength/==GT" [~1] forall t n.
    GHC.gtInt (length t) n = compareLength t n == GT
  #-}

{-# RULES
"JSSTRING >=N/length -> compareLength//=LT" [~1] forall t n.
    GHC.geInt (length t) n = compareLength t n /= LT
  #-}

-- -----------------------------------------------------------------------------
-- * Transformations
-- | /O(n)/ 'map' @f@ @t@ is the 'JSString' obtained by applying @f@ to
-- each element of @t@.
--
-- Example:
--
-- >>> let message = pack "I am not angry. Not at all."
-- >>> T.map (\c -> if c == '.' then '!' else c) message
-- "I am not angry! Not at all!"
--
-- Subject to fusion.  Performs replacement on invalid scalar values.
map :: (Char -> Char) -> JSString -> JSString
map f t = unstream (S.map (safe . f) (stream t))
{-# INLINE [1] map #-}

-- | /O(n)/ The 'intercalate' function takes a 'JSString' and a list of
-- 'JSString's and concatenates the list after interspersing the first
-- argument between each element of the list.
intercalate :: JSString -> [JSString] -> JSString
intercalate i xs = rnf xs `seq` js_intercalate i (unsafeCoerce xs)
{-# INLINE [1] intercalate #-}

-- | /O(n)/ The 'intersperse' function takes a character and places it
-- between the characters of a 'JSString'.
--
-- Example:
--
-- >>> T.intersperse '.' "SHIELD"
-- "S.H.I.E.L.D"
--
-- Subject to fusion.  Performs replacement on invalid scalar values.
intersperse     :: Char -> JSString -> JSString
intersperse c x = js_intersperse c x
{-# INLINE [1] intersperse #-}

{-# RULES
"JSSTRING intersperse -> fused" [~1] forall c x.
    intersperse c x = unstream (S.intersperse (safe c) (stream x))
"JSSTRING intersperse -> unfused" [1] forall c x.
    unstream (S.intersperse (safe c) (stream x)) = intersperse c x
 #-}

-- | /O(n)/ Reverse the characters of a string.
--
-- Example:
--
-- >>> T.reverse "desrever"
-- "reversed"
--
-- Subject to fusion.
reverse :: JSString -> JSString
reverse x = js_reverse x -- S.reverse (stream x)
{-# INLINE [1] reverse #-}

{-# RULES
"JSSTRING reverse -> fused" [~1] forall x.
    reverse x = S.reverse (stream x)
"JSSTRING reverse -> unfused" [1] forall x.
    S.reverse (stream x) = reverse x
 #-}

-- | /O(m+n)/ Replace every non-overlapping occurrence of @needle@ in
-- @haystack@ with @replacement@.
--
-- This function behaves as though it was defined as follows:
--
-- @
-- replace needle replacement haystack =
--   'intercalate' replacement ('splitOn' needle haystack)
-- @
--
-- As this suggests, each occurrence is replaced exactly once.  So if
-- @needle@ occurs in @replacement@, that occurrence will /not/ itself
-- be replaced recursively:
--
-- >>> replace "oo" "foo" "oo"
-- "foo"
--
-- In cases where several instances of @needle@ overlap, only the
-- first one will be replaced:
--
-- >>> replace "ofo" "bar" "ofofo"
-- "barfo"
--
-- In (unlikely) bad cases, this function's time complexity degrades
-- towards /O(n*m)/.
replace :: JSString
        -- ^ @needle@ to search for.  If this string is empty, an
        -- error will occur.
        -> JSString
        -- ^ @replacement@ to replace @needle@ with.
        -> JSString
        -- ^ @haystack@ in which to search.
        -> JSString
replace needle replacement haystack
  | js_null needle = emptyError "replace"
  | otherwise      = js_replace needle replacement haystack
{-# INLINE replace #-}

-- ----------------------------------------------------------------------------
-- ** Case conversions (folds)

-- $case
--
-- When case converting 'JSString' values, do not use combinators like
-- @map toUpper@ to case convert each character of a string
-- individually, as this gives incorrect results according to the
-- rules of some writing systems.  The whole-string case conversion
-- functions from this module, such as @toUpper@, obey the correct
-- case conversion rules.  As a result, these functions may map one
-- input character to two or three output characters. For examples,
-- see the documentation of each function.
--
-- /Note/: In some languages, case conversion is a locale- and
-- context-dependent operation. The case conversion functions in this
-- module are /not/ locale sensitive. Programs that require locale
-- sensitivity should use appropriate versions of the
-- <http://hackage.haskell.org/package/text-icu-0.6.3.7/docs/Data-Text-ICU.html#g:4 case mapping functions from the text-icu package >.

-- | /O(n)/ Convert a string to folded case.  Subject to fusion.
--
-- This function is mainly useful for performing caseless (also known
-- as case insensitive) string comparisons.
--
-- A string @x@ is a caseless match for a string @y@ if and only if:
--
-- @toCaseFold x == toCaseFold y@
--
-- The result string may be longer than the input string, and may
-- differ from applying 'toLower' to the input string.  For instance,
-- the Armenian small ligature \"&#xfb13;\" (men now, U+FB13) is case
-- folded to the sequence \"&#x574;\" (men, U+0574) followed by
-- \"&#x576;\" (now, U+0576), while the Greek \"&#xb5;\" (micro sign,
-- U+00B5) is case folded to \"&#x3bc;\" (small letter mu, U+03BC)
-- instead of itself.
toCaseFold :: JSString -> JSString
toCaseFold t = unstream (S.toCaseFold (stream t))
{-# INLINE toCaseFold #-}

-- | /O(n)/ Convert a string to lower case, using simple case
-- conversion.  Subject to fusion.
--
-- The result string may be longer than the input string.  For
-- instance, \"&#x130;\" (Latin capital letter I with dot above,
-- U+0130) maps to the sequence \"i\" (Latin small letter i, U+0069)
-- followed by \" &#x307;\" (combining dot above, U+0307).
toLower :: JSString -> JSString
toLower x = js_toLower x
{-# INLINE [1] toLower #-}

{-# RULES
"JSSTRING toLower -> fused" [~1] forall x.
    toLower x = unstream (S.toLower (stream x))
"JSSTRING toLower -> unfused" [1] forall x.
    unstream (S.toLower (stream x)) = toLower x
 #-}

-- | /O(n)/ Convert a string to upper case, using simple case
-- conversion.  Subject to fusion.
--
-- The result string may be longer than the input string.  For
-- instance, the German \"&#xdf;\" (eszett, U+00DF) maps to the
-- two-letter sequence \"SS\".
toUpper :: JSString -> JSString
toUpper x = js_toUpper x
{-# INLINE [1] toUpper #-}

{-# RULES
"JSSTRING toUpper -> fused" [~1] forall x.
    toUpper x = unstream (S.toUpper(stream x))
"JSSTRING toUpper -> unfused" [1] forall x.
    unstream (S.toUpper (stream x)) = toUpper x
 #-}

-- | /O(n)/ Convert a string to title case, using simple case
-- conversion. Subject to fusion.
--
-- The first letter of the input is converted to title case, as is
-- every subsequent letter that immediately follows a non-letter.
-- Every letter that immediately follows another letter is converted
-- to lower case.
--
-- The result string may be longer than the input string. For example,
-- the Latin small ligature &#xfb02; (U+FB02) is converted to the
-- sequence Latin capital letter F (U+0046) followed by Latin small
-- letter l (U+006C).
--
-- /Note/: this function does not take language or culture specific
-- rules into account. For instance, in English, different style
-- guides disagree on whether the book name \"The Hill of the Red
-- Fox\" is correctly title cased&#x2014;but this function will
-- capitalize /every/ word.
toTitle :: JSString -> JSString
toTitle t = unstream (S.toTitle (stream t))
{-# INLINE toTitle #-}

-- | /O(n)/ Left-justify a string to the given length, using the
-- specified fill character on the right. Subject to fusion.
-- Performs replacement on invalid scalar values.
--
-- Examples:
--
-- >>> justifyLeft 7 'x' "foo"
-- "fooxxxx"
--
-- >>> justifyLeft 3 'x' "foobar"
-- "foobar"
justifyLeft :: Int -> Char -> JSString -> JSString
justifyLeft k c t
    | len >= k  = t
    | otherwise = t `append` replicateChar (k-len) c
  where len = length t
{-# INLINE [1] justifyLeft #-}

{-# RULES
"JSSTRING justifyLeft -> fused" [~1] forall k c t.
    justifyLeft k c t = unstream (S.justifyLeftI k c (stream t))
"JSSTRING justifyLeft -> unfused" [1] forall k c t.
    unstream (S.justifyLeftI k c (stream t)) = justifyLeft k c t
  #-}

-- | /O(n)/ Right-justify a string to the given length, using the
-- specified fill character on the left.  Performs replacement on
-- invalid scalar values.
--
-- Examples:
--
-- >>> justifyRight 7 'x' "bar"
-- "xxxxbar"
--
-- >>> justifyRight 3 'x' "foobar"
-- "foobar"
justifyRight :: Int -> Char -> JSString -> JSString
justifyRight k c t
    | len >= k  = t
    | otherwise = replicateChar (k-len) c `append` t
  where len = length t
{-# INLINE justifyRight #-}

-- | /O(n)/ Center a string to the given length, using the specified
-- fill character on either side.  Performs replacement on invalid
-- scalar values.
--
-- Examples:
--
-- >>> center 8 'x' "HS"
-- "xxxHSxxx"
center :: Int -> Char -> JSString -> JSString
center k c t
    | len >= k  = t
    | otherwise = replicateChar l c `append` t `append` replicateChar r c
  where len = length t
        d   = k - len
        r   = d `quot` 2
        l   = d - r
{-# INLINE center #-}

-- | /O(n)/ The 'transpose' function transposes the rows and columns
-- of its 'JSString' argument.  Note that this function uses 'pack',
-- 'unpack', and the list version of transpose, and is thus not very
-- efficient.
--
-- Examples:
--
-- >>> transpose ["green","orange"]
-- ["go","rr","ea","en","ng","e"]
--
-- >>> transpose ["blue","red"]
-- ["br","le","ud","e"]
transpose :: [JSString] -> [JSString]
transpose ts = P.map pack (L.transpose (P.map unpack ts))

-- -----------------------------------------------------------------------------
-- * Reducing 'JSString's (folds)

-- | /O(n)/ 'foldl', applied to a binary operator, a starting value
-- (typically the left-identity of the operator), and a 'JSString',
-- reduces the 'JSString' using the binary operator, from left to right.
-- Subject to fusion.
foldl :: (a -> Char -> a) -> a -> JSString -> a
foldl f z t = S.foldl f z (stream t)
{-# INLINE foldl #-}

-- | /O(n)/ A strict version of 'foldl'.  Subject to fusion.
foldl' :: (a -> Char -> a) -> a -> JSString -> a
foldl' f z t = S.foldl' f z (stream t)
{-# INLINE foldl' #-}

-- | /O(n)/ A variant of 'foldl' that has no starting value argument,
-- and thus must be applied to a non-empty 'JSString'.  Subject to fusion.
foldl1 :: (Char -> Char -> Char) -> JSString -> Char
foldl1 f t = S.foldl1 f (stream t)
{-# INLINE foldl1 #-}

-- | /O(n)/ A strict version of 'foldl1'.  Subject to fusion.
foldl1' :: (Char -> Char -> Char) -> JSString -> Char
foldl1' f t = S.foldl1' f (stream t)
{-# INLINE foldl1' #-}

-- | /O(n)/ 'foldr', applied to a binary operator, a starting value
-- (typically the right-identity of the operator), and a 'JSString',
-- reduces the 'JSString' using the binary operator, from right to left.
-- Subject to fusion.
foldr :: (Char -> a -> a) -> a -> JSString -> a
foldr f z t = S.foldr f z (stream t)
{-# INLINE foldr #-}

-- | /O(n)/ A variant of 'foldr' that has no starting value argument,
-- and thus must be applied to a non-empty 'JSString'.  Subject to
-- fusion.
foldr1 :: (Char -> Char -> Char) -> JSString -> Char
foldr1 f t = S.foldr1 f (stream t)
{-# INLINE foldr1 #-}

-- -----------------------------------------------------------------------------
-- ** Special folds

-- | /O(n)/ Concatenate a list of 'JSString's.
concat :: [JSString] -> JSString
concat xs = rnf xs `seq` js_concat (unsafeCoerce xs)
{-  case ts' of
              [] -> empty
              [t] -> t
              _ -> Text (A.run go) 0 len
  where
    ts' = L.filter (not . null) ts
    len = sumP "concat" $ L.map lengthWord16 ts'
    go :: ST s (A.MArray s)
    go = do
      arr <- A.new len
      let step i (Text a o l) =
            let !j = i + l in A.copyI arr i a o j >> return j
      foldM step 0 ts' >> return arr
-}

-- | /O(n)/ Map a function over a 'JSString' that results in a 'JSString', and
-- concatenate the results.
concatMap :: (Char -> JSString) -> JSString -> JSString
concatMap f = concat . foldr ((:) . f) []
{-# INLINE concatMap #-}

-- | /O(n)/ 'any' @p@ @t@ determines whether any character in the
-- 'JSString' @t@ satisfies the predicate @p@. Subject to fusion.
any :: (Char -> Bool) -> JSString -> Bool
any p t = S.any p (stream t)
{-# INLINE any #-}

-- | /O(n)/ 'all' @p@ @t@ determines whether all characters in the
-- 'JSString' @t@ satisify the predicate @p@. Subject to fusion.
all :: (Char -> Bool) -> JSString -> Bool
all p t = S.all p (stream t)
{-# INLINE all #-}

-- | /O(n)/ 'maximum' returns the maximum value from a 'JSString', which
-- must be non-empty. Subject to fusion.
maximum :: JSString -> Char
maximum t = S.maximum (stream t)
{-# INLINE maximum #-}

-- | /O(n)/ 'minimum' returns the minimum value from a 'JSString', which
-- must be non-empty. Subject to fusion.
minimum :: JSString -> Char
minimum t = S.minimum (stream t)
{-# INLINE minimum #-}

-- -----------------------------------------------------------------------------
-- * Building 'JSString's

-- | /O(n)/ 'scanl' is similar to 'foldl', but returns a list of
-- successive reduced values from the left. Subject to fusion.
-- Performs replacement on invalid scalar values.
--
-- > scanl f z [x1, x2, ...] == [z, z `f` x1, (z `f` x1) `f` x2, ...]
--
-- Note that
--
-- > last (scanl f z xs) == foldl f z xs.
scanl :: (Char -> Char -> Char) -> Char -> JSString -> JSString
scanl f z t = unstream (S.scanl g z (stream t))
    where g a b = safe (f a b)
{-# INLINE scanl #-}

-- | /O(n)/ 'scanl1' is a variant of 'scanl' that has no starting
-- value argument.  Subject to fusion.  Performs replacement on
-- invalid scalar values.
--
-- > scanl1 f [x1, x2, ...] == [x1, x1 `f` x2, ...]
scanl1 :: (Char -> Char -> Char) -> JSString -> JSString
scanl1 f x = case uncons x of
              Just (h, t) -> scanl f h t
              Nothing     -> empty
{-# INLINE scanl1 #-}

-- | /O(n)/ 'scanr' is the right-to-left dual of 'scanl'.  Performs
-- replacement on invalid scalar values.
--
-- > scanr f v == reverse . scanl (flip f) v . reverse
scanr :: (Char -> Char -> Char) -> Char -> JSString -> JSString
scanr f z = S.reverse . S.reverseScanr g z . S.reverseStream
    where g a b = safe (f a b)
{-# INLINE scanr #-}

-- | /O(n)/ 'scanr1' is a variant of 'scanr' that has no starting
-- value argument.  Subject to fusion.  Performs replacement on
-- invalid scalar values.
scanr1 :: (Char -> Char -> Char) -> JSString -> JSString
scanr1 f t | null t    = empty
           | otherwise = scanr f (last t) (init t)
{-# INLINE scanr1 #-}

-- | /O(n)/ Like a combination of 'map' and 'foldl''. Applies a
-- function to each element of a 'JSString', passing an accumulating
-- parameter from left to right, and returns a final 'JSString'.  Performs
-- replacement on invalid scalar values.
mapAccumL :: (a -> Char -> (a,Char)) -> a -> JSString -> (a, JSString)
mapAccumL f z0 = S.mapAccumL g z0 . stream
    where g a b = second safe (f a b)
{-# INLINE mapAccumL #-}

-- | The 'mapAccumR' function behaves like a combination of 'map' and
-- a strict 'foldr'; it applies a function to each element of a
-- 'JSString', passing an accumulating parameter from right to left, and
-- returning a final value of this accumulator together with the new
-- 'JSString'.
-- Performs replacement on invalid scalar values.
mapAccumR :: (a -> Char -> (a,Char)) -> a -> JSString -> (a, JSString)
mapAccumR f z0 = second reverse . S.mapAccumL g z0 . S.reverseStream
    where g a b = second safe (f a b)
{-# INLINE mapAccumR #-}

-- -----------------------------------------------------------------------------
-- ** Generating and unfolding 'JSString's

-- | /O(n*m)/ 'replicate' @n@ @t@ is a 'JSString' consisting of the input
-- @t@ repeated @n@ times.
replicate :: Int -> JSString -> JSString
replicate (I# n) t = js_replicate n t
{-                t@(Text a o l)
    | n <= 0 || l <= 0       = empty
    | n == 1                 = t
    | isSingleton t          = replicateChar n (unsafeHead t)
    | otherwise              = Text (A.run x) 0 len
  where
    len = l `mul` n
    x :: ST s (A.MArray s)
    x = do
      arr <- A.new len
      let loop !d !i | i >= n    = return arr
                     | otherwise = let m = d + l
                                   in A.copyI arr d a o m >> loop m (i+1)
      loop 0 0 -}
{-# INLINE [1] replicate #-}

{-# RULES
"JSSTRING replicate/singleton -> replicateChar" [~1] forall n c.
    replicate n (singleton c) = replicateChar n c
  #-}

-- | /O(n)/ 'replicateChar' @n@ @c@ is a 'JSString' of length @n@ with @c@ the
-- value of every element. Subject to fusion.
replicateChar :: Int -> Char -> JSString
replicateChar n c = js_replicateChar n c
{-# INLINE [1] replicateChar #-}

{-# RULES
"JSSTRING replicateChar -> fused" [~1] forall n c.
    replicateChar n c = unstream (S.replicateCharI n (safe c))
"JSSTRING replicateChar -> unfused" [1] forall n c.
    unstream (S.replicateCharI n (safe c)) = replicateChar n c
  #-}

-- | /O(n)/, where @n@ is the length of the result. The 'unfoldr'
-- function is analogous to the List 'L.unfoldr'. 'unfoldr' builds a
-- 'JSString' from a seed value. The function takes the element and
-- returns 'Nothing' if it is done producing the 'JSString', otherwise
-- 'Just' @(a,b)@.  In this case, @a@ is the next 'Char' in the
-- string, and @b@ is the seed value for further production. Subject
-- to fusion.  Performs replacement on invalid scalar values.
unfoldr     :: (a -> Maybe (Char,a)) -> a -> JSString
unfoldr f s = unstream (S.unfoldr (firstf safe . f) s)
{-# INLINE unfoldr #-}

-- | /O(n)/ Like 'unfoldr', 'unfoldrN' builds a 'JSString' from a seed
-- value. However, the length of the result should be limited by the
-- first argument to 'unfoldrN'. This function is more efficient than
-- 'unfoldr' when the maximum length of the result is known and
-- correct, otherwise its performance is similar to 'unfoldr'. Subject
-- to fusion.  Performs replacement on invalid scalar values.
unfoldrN     :: Int -> (a -> Maybe (Char,a)) -> a -> JSString
unfoldrN n f s = unstream (S.unfoldrN n (firstf safe . f) s)
{-# INLINE unfoldrN #-}

-- -----------------------------------------------------------------------------
-- * Substrings

-- | /O(n)/ 'take' @n@, applied to a 'JSString', returns the prefix of the
-- 'JSString' of length @n@, or the 'JSString' itself if @n@ is greater than
-- the length of the JSString. Subject to fusion.
take :: Int -> JSString -> JSString
take (I# n) t = js_take n t
{-           t@(Text arr off len)
    | n <= 0    = empty
    | n >= len  = t
    | otherwise = text arr off (iterN n t) -}
{-# INLINE [1] take #-}
{-
iterN :: Int -> JSString -> Int
iterN n t@(Text _arr _off len) = loop 0 0
  where loop !i !cnt
            | i >= len || cnt >= n = i
            | otherwise            = loop (i+d) (cnt+1)
          where d = iter_ t i
-}
{-# RULES
"JSSTRING take -> fused" [~1] forall n t.
    take n t = unstream (S.take n (stream t))
"JSSTRING take -> unfused" [1] forall n t.
    unstream (S.take n (stream t)) = take n t
  #-}

-- | /O(n)/ 'takeEnd' @n@ @t@ returns the suffix remaining after
-- taking @n@ characters from the end of @t@.
--
-- Examples:
--
-- >>> takeEnd 3 "foobar"
-- "bar"
--
takeEnd :: Int -> JSString -> JSString
takeEnd (I# n) x = js_takeEnd n x
{-
iterNEnd :: Int -> JSString -> Int
iterNEnd n t@(Text _arr _off len) = loop (len-1) n
  where loop i !m
          | i <= 0    = 0
          | m <= 1    = i
          | otherwise = loop (i+d) (m-1)
          where d = reverseIter_ t i
-}
-- | /O(n)/ 'drop' @n@, applied to a 'JSString', returns the suffix of the
-- 'JSString' after the first @n@ characters, or the empty 'JSString' if @n@
-- is greater than the length of the 'JSString'. Subject to fusion.
drop :: Int -> JSString -> JSString
drop (I# n) x = js_drop n x
{-# INLINE [1] drop #-}

{-# RULES
"JSSTRING drop -> fused" [~1] forall n t.
    drop n t = unstream (S.drop n (stream t))
"JSSTRING drop -> unfused" [1] forall n t.
    unstream (S.drop n (stream t)) = drop n t
  #-}

-- | /O(n)/ 'dropEnd' @n@ @t@ returns the prefix remaining after
-- dropping @n@ characters from the end of @t@.
--
-- Examples:
--
-- >>> dropEnd 3 "foobar"
-- "foo"
--
dropEnd :: Int -> JSString -> JSString
dropEnd n x = js_dropEnd n x

-- | /O(n)/ 'takeWhile', applied to a predicate @p@ and a 'JSString',
-- returns the longest prefix (possibly empty) of elements that
-- satisfy @p@.  Subject to fusion.
takeWhile :: (Char -> Bool) -> JSString -> JSString
takeWhile p x = loop 0# (js_length x)
  where loop i l | isTrue# (i >=# l) = x
                 | otherwise =
                     case js_index i x of
                       c | p (C# (chr# c)) -> loop (i +# charWidth c) l
                       _                   -> js_substr 0# i x
{-# INLINE [1] takeWhile #-}

{-# RULES
"TEXT takeWhile -> fused" [~1] forall p t.
    takeWhile p t = unstream (S.takeWhile p (stream t))
"TEXT takeWhile -> unfused" [1] forall p t.
    unstream (S.takeWhile p (stream t)) = takeWhile p t
  #-}

-- | /O(n)/ 'takeWhileEnd', applied to a predicate @p@ and a 'Text',
-- returns the longest suffix (possibly empty) of elements that
-- satisfy @p@.
-- Examples:
--
-- >>> takeWhileEnd (=='o') "foo"
-- "oo"
--
takeWhileEnd :: (Char -> Bool) -> JSString -> JSString
takeWhileEnd p x = loop (js_length x -# 1#)
  where loop -1# = empty
        loop i   = case js_uncheckedIndexR i x of
                     c | p (C# (chr# c)) -> loop (i -# charWidth c)
                     _                   -> js_substr1 (i +# 1#) x
{-# INLINE takeWhileEnd #-}

-- | /O(n)/ 'dropWhile' @p@ @t@ returns the suffix remaining after
-- 'takeWhile' @p@ @t@. Subject to fusion.
dropWhile :: (Char -> Bool) -> JSString -> JSString
dropWhile p x = loop 0# (js_length x)
  where loop i l | isTrue# (i >=# l) = empty
                 | otherwise =
                     case js_uncheckedIndex i x of
                      c | p (C# (chr# c)) -> loop (i +# charWidth c) l
                      _                   -> js_substr1 i x
{-# INLINE [1] dropWhile #-}

{-# RULES
"TEXT dropWhile -> fused" [~1] forall p t.
    dropWhile p t = unstream (S.dropWhile p (stream t))
"TEXT dropWhile -> unfused" [1] forall p t.
    unstream (S.dropWhile p (stream t)) = dropWhile p t
  #-}

-- | /O(n)/ 'dropWhileEnd' @p@ @t@ returns the prefix remaining after
-- dropping characters that satisfy the predicate @p@ from the end of
-- @t@.  Subject to fusion.
-- Examples:
--
-- >>> dropWhileEnd (=='.') "foo..."
-- "foo"
dropWhileEnd :: (Char -> Bool) -> JSString -> JSString
dropWhileEnd p x = loop (js_length x -# 1#)
  where loop -1# = empty
        loop i   = case js_uncheckedIndexR i x of
                     c | p (C# (chr# c)) -> loop (i -# charWidth c)
                     _                   -> js_substr 0# (i +# 1#) x
{-# INLINE [1] dropWhileEnd #-}

{-# RULES
"TEXT dropWhileEnd -> fused" [~1] forall p t.
    dropWhileEnd p t = S.reverse (S.dropWhile p (S.reverseStream t))
"TEXT dropWhileEnd -> unfused" [1] forall p t.
    S.reverse (S.dropWhile p (S.reverseStream t)) = dropWhileEnd p t
  #-}

-- | /O(n)/ 'dropAround' @p@ @t@ returns the substring remaining after
-- dropping characters that satisfy the predicate @p@ from both the
-- beginning and end of @t@.  Subject to fusion.
dropAround :: (Char -> Bool) -> JSString -> JSString
dropAround p = dropWhile p . dropWhileEnd p
{-# INLINE [1] dropAround #-}

-- | /O(n)/ Remove leading white space from a string.  Equivalent to:
--
-- > dropWhile isSpace
stripStart :: JSString -> JSString
stripStart = dropWhile isSpace
{-# INLINE [1] stripStart #-}

-- | /O(n)/ Remove trailing white space from a string.  Equivalent to:
--
-- > dropWhileEnd isSpace
stripEnd :: JSString -> JSString
stripEnd = dropWhileEnd isSpace
{-# INLINE [1] stripEnd #-}

-- | /O(n)/ Remove leading and trailing white space from a string.
-- Equivalent to:
--
-- > dropAround isSpace
strip :: JSString -> JSString
strip = dropAround isSpace
{-# INLINE [1] strip #-}

-- | /O(n)/ 'splitAt' @n t@ returns a pair whose first element is a
-- prefix of @t@ of length @n@, and whose second is the remainder of
-- the string. It is equivalent to @('take' n t, 'drop' n t)@.
splitAt :: Int -> JSString -> (JSString, JSString)
splitAt (I# n) x = case js_splitAt n x of (# y, z #) -> (y, z)
{-# INLINE splitAt #-}

-- | /O(n)/ 'span', applied to a predicate @p@ and text @t@, returns
-- a pair whose first element is the longest prefix (possibly empty)
-- of @t@ of elements that satisfy @p@, and whose second is the
-- remainder of the list.
span :: (Char -> Bool) -> JSString -> (JSString, JSString)
span p x = case js_length x of
            0# -> (empty, empty)
            l  -> let c0 = js_uncheckedIndex 0# x
                  in if p (C# (chr# c0)) then loop 0# l else (empty, x)
  where
    loop i l
      | isTrue# (i >=# l) = (x, empty)
      | otherwise         =
          let c = js_uncheckedIndex i x
          in  if p (C# (chr# c))
              then loop (i +# charWidth c) l
              else (js_substr 0# i x, js_substr1 i x)
{-# INLINE span #-}

-- | /O(n)/ 'break' is like 'span', but the prefix returned is
-- over elements that fail the predicate @p@.
break :: (Char -> Bool) -> JSString -> (JSString, JSString)
break p = span (not . p)
{-# INLINE break #-}

-- | /O(n)/ Group characters in a string according to a predicate.
groupBy :: (Char -> Char -> Bool) -> JSString -> [JSString]
groupBy p x =
  case js_length x of
   0# -> []
   l  -> let c0 = js_uncheckedIndex 0# x
         in  loop (C# (chr# c0)) 0# (charWidth c0) l
  where
    loop b s i l
      | isTrue# (i >=# l) =
          if isTrue# (i ># s) then [js_substr1 s x] else []
      | otherwise =
          let c  = js_uncheckedIndex i x
              c' = C# (chr# c)
              i' = i +# charWidth c
          in  if   p b c'
              then loop b s i' l
              else js_substring s i x : loop c' i i' l

{-
-- | Returns the /array/ index (in units of 'Word16') at which a
-- character may be found.  This is /not/ the same as the logical
-- index returned by e.g. 'findIndex'.
findAIndexOrEnd :: (Char -> Bool) -> JSString -> Int
findAIndexOrEnd q t@(Text _arr _off len) = go 0
    where go !i | i >= len || q c       = i
                | otherwise             = go (i+d)
                where Iter c d          = iter t i
-}

-- | /O(n)/ Group characters in a string by equality.
group :: JSString -> [JSString]
group x = group' x -- fixme, implement lazier version
{-# INLINE group #-}

group' :: JSString -> [JSString]
group' x = unsafeCoerce (js_group x)
{-# INLINE group' #-}

-- | /O(n^2)/ Return all initial segments of the given 'JSString', shortest
-- first.
inits :: JSString -> [JSString]
inits x = empty : case js_length x of
                   0# -> []
                   l  -> loop (js_charWidthAt 0# x) l
    where
      loop i l
        | isTrue# (i >=# l) = [x]
        | otherwise         =
            js_substr 0# i x : loop (i +# js_charWidthAt i x) l

-- | /O(n^2)/ Return all final segments of the given 'JSString', longest
-- first.
tails :: JSString -> [JSString]
tails x =
  case js_length x of -- this could be less strict
    0# -> [empty]
    l  -> loop 0# l
  where
    loop i l
      | isTrue# (i >=# l) = [empty]
      | otherwise         =
          js_substr1 i x : loop (i +# js_charWidthAt i x) l

-- $split
--
-- Splitting functions in this library do not perform character-wise
-- copies to create substrings; they just construct new 'JSString's that
-- are slices of the original.

-- | /O(m+n)/ Break a 'JSString' into pieces separated by the first 'JSString'
-- argument (which cannot be empty), consuming the delimiter. An empty
-- delimiter is invalid, and will cause an error to be raised.
--
-- Examples:
--
-- >>> splitOn "\r\n" "a\r\nb\r\nd\r\ne"
-- ["a","b","d","e"]
--
-- >>> splitOn "aaa"  "aaaXaaaXaaaXaaa"
-- ["","X","X","X",""]
--
-- >>> splitOn "x"    "x"
-- ["",""]
--
-- and
--
-- > intercalate s . splitOn s         == id
-- > splitOn (singleton c)             == split (==c)
--
-- (Note: the string @s@ to split on above cannot be empty.)
--
-- In (unlikely) bad cases, this function's time complexity degrades
-- towards /O(n*m)/.
splitOn :: JSString
        -- ^ String to split on. If this string is empty, an error
        -- will occur.
        -> JSString
        -- ^ Input text.
        -> [JSString]
splitOn = splitOn' -- fixme
{-
splitOn pat src
  | null pat  = emptyError "splitOn"
  | otherwise = go 0#
  where
    go i = case js_splitOn1 i pat src of
             (# n, h #) -> case n of
                             -1# -> []
                             n'  -> h : go n'
-}
{-# INLINE [1] splitOn #-}

-- RULES
-- "JSSTRING splitOn/singleton -> split/==" [~1] forall c t.
--    splitOn (singleton c) t = split (==c) t
--

splitOn' :: JSString
         -- ^ String to split on. If this string is empty, an error
         -- will occur.
         -> JSString
         -- ^ Input text.
         -> [JSString]
splitOn' pat src
  | null pat  = emptyError "splitOn'"
  | otherwise = unsafeCoerce (js_splitOn pat src)
{-# NOINLINE splitOn' #-}
--- {-# INLINE [1] splitOn' #-}

-- | /O(n)/ Splits a 'JSString' into components delimited by separators,
-- where the predicate returns True for a separator element.  The
-- resulting components do not contain the separators.  Two adjacent
-- separators result in an empty component in the output.  eg.
--
-- >>> split (=='a') "aabbaca"
-- ["","","bb","c",""]
--
-- >>> split (=='a') ""
-- [""]
split :: (Char -> Bool) -> JSString -> [JSString]
split p x = case js_length x of
             0# -> [empty]
             l  -> loop 0# 0# l
      where
        loop s i l
          | isTrue# (i >=# l) = [js_substr s i x]
          | otherwise         =
              let ch = js_uncheckedIndex i x
                  i' = i +# charWidth ch
              in  if p (C# (chr# ch))
                  then js_substr s (i -# s) x : loop i' i' l
                  else loop s i' l
{-# INLINE split #-}

-- | /O(n)/ Splits a 'JSString' into components of length @k@.  The last
-- element may be shorter than the other chunks, depending on the
-- length of the input. Examples:
--
-- >>> chunksOf 3 "foobarbaz"
-- ["foo","bar","baz"]
--
-- >>> chunksOf 4 "haskell.org"
-- ["hask","ell.","org"]
chunksOf :: Int -> JSString -> [JSString]
chunksOf (I# k) p = go 0#
  where
    go i = case js_chunksOf1 k i p of
            (# n, c #) -> case n of
                            -1# -> []
                            _   -> c : go n
{-# INLINE chunksOf #-}

-- | /O(n)/ Splits a 'JSString' into components of length @k@.  The last
-- element may be shorter than the other chunks, depending on the
-- length of the input. Examples:
--
-- > chunksOf 3 "foobarbaz"   == ["foo","bar","baz"]
-- > chunksOf 4 "haskell.org" == ["hask","ell.","org"]
chunksOf' :: Int -> JSString -> [JSString]
chunksOf' (I# k) p = unsafeCoerce (js_chunksOf k p)
{-# INLINE chunksOf' #-}

-- ----------------------------------------------------------------------------
-- * Searching

-------------------------------------------------------------------------------
-- ** Searching with a predicate

-- | /O(n)/ The 'find' function takes a predicate and a 'JSString', and
-- returns the first element matching the predicate, or 'Nothing' if
-- there is no such element.
find :: (Char -> Bool) -> JSString -> Maybe Char
find p t = S.findBy p (stream t)
{-# INLINE find #-}

-- | /O(n)/ The 'partition' function takes a predicate and a 'JSString',
-- and returns the pair of 'JSString's with elements which do and do not
-- satisfy the predicate, respectively; i.e.
--
-- > partition p t == (filter p t, filter (not . p) t)
partition :: (Char -> Bool) -> JSString -> (JSString, JSString)
partition p t = (filter p t, filter (not . p) t)
{-# INLINE partition #-}

-- | /O(n)/ 'filter', applied to a predicate and a 'JSString',
-- returns a 'JSString' containing those characters that satisfy the
-- predicate.
filter :: (Char -> Bool) -> JSString -> JSString
filter p t = unstream (S.filter p (stream t))
{-# INLINE filter #-}

-- | /O(n+m)/ Find the first instance of @needle@ (which must be
-- non-'null') in @haystack@.  The first element of the returned tuple
-- is the prefix of @haystack@ before @needle@ is matched.  The second
-- is the remainder of @haystack@, starting with the match.
--
-- Examples:
--
-- >>> breakOn "::" "a::b::c"
-- ("a","::b::c")
--
-- >>> breakOn "/" "foobar"
-- ("foobar","")
--
-- Laws:
--
-- > append prefix match == haystack
-- >   where (prefix, match) = breakOn needle haystack
--
-- If you need to break a string by a substring repeatedly (e.g. you
-- want to break on every instance of a substring), use 'breakOnAll'
-- instead, as it has lower startup overhead.
--
-- In (unlikely) bad cases, this function's time complexity degrades
-- towards /O(n*m)/.
breakOn :: JSString -> JSString -> (JSString, JSString)
breakOn pat src
  | null pat  = emptyError "breakOn"
  | otherwise = case js_breakOn pat src of (# y, z #) -> (y, z)
{-# INLINE breakOn #-}

-- | /O(n+m)/ Similar to 'breakOn', but searches from the end of the
-- string.
--
-- The first element of the returned tuple is the prefix of @haystack@
-- up to and including the last match of @needle@.  The second is the
-- remainder of @haystack@, following the match.
--
-- >>> breakOnEnd "::" "a::b::c"
-- ("a::b::","c")
breakOnEnd :: JSString -> JSString -> (JSString, JSString)
breakOnEnd pat src
  | null pat  = emptyError "breakOnEnd"
  | otherwise = case js_breakOnEnd pat src of (# y, z #) -> (y, z)
{-# INLINE breakOnEnd #-}

-- | /O(n+m)/ Find all non-overlapping instances of @needle@ in
-- @haystack@.  Each element of the returned list consists of a pair:
--
-- * The entire string prior to the /k/th match (i.e. the prefix)
--
-- * The /k/th match, followed by the remainder of the string
--
-- Examples:
--
-- >>> breakOnAll "::" ""
-- []
--
-- >>> breakOnAll "/" "a/b/c/"
-- [("a","/b/c/"),("a/b","/c/"),("a/b/c","/")]
--
-- In (unlikely) bad cases, this function's time complexity degrades
-- towards /O(n*m)/.
--
-- The @needle@ parameter may not be empty.
breakOnAll :: JSString              -- ^ @needle@ to search for
           -> JSString              -- ^ @haystack@ in which to search
           -> [(JSString, JSString)]
breakOnAll pat src
    | null pat  = emptyError "breakOnAll"
    | otherwise = go 0#
  where
    go i = case js_breakOnAll1 i pat src of
              (# n, x, y #) -> case n of
                -1# -> []
                _   -> (x,y) : go n
{-# INLINE breakOnAll #-}

breakOnAll' :: JSString              -- ^ @needle@ to search for
            -> JSString              -- ^ @haystack@ in which to search
            -> [(JSString, JSString)]
breakOnAll' pat src
    | null pat  = emptyError "breakOnAll'"
    | otherwise = unsafeCoerce (js_breakOnAll pat src)
{-# INLINE breakOnAll' #-}

-------------------------------------------------------------------------------
-- ** Indexing 'JSString's

-- $index
--
-- If you think of a 'JSString' value as an array of 'Char' values (which
-- it is not), you run the risk of writing inefficient code.
--
-- An idiom that is common in some languages is to find the numeric
-- offset of a character or substring, then use that number to split
-- or trim the searched string.  With a 'JSString' value, this approach
-- would require two /O(n)/ operations: one to perform the search, and
-- one to operate from wherever the search ended.
--
-- For example, suppose you have a string that you want to split on
-- the substring @\"::\"@, such as @\"foo::bar::quux\"@. Instead of
-- searching for the index of @\"::\"@ and taking the substrings
-- before and after that index, you would instead use @breakOnAll \"::\"@.

-- | /O(n)/ 'JSString' index (subscript) operator, starting from 0.
index :: JSString -> Int -> Char
index t n = S.index (stream t) n
{-# INLINE index #-}

-- | /O(n)/ The 'findIndex' function takes a predicate and a 'JSString'
-- and returns the index of the first element in the 'JSString' satisfying
-- the predicate. Subject to fusion.
findIndex :: (Char -> Bool) -> JSString -> Maybe Int
findIndex p t = S.findIndex p (stream t)
{-# INLINE findIndex #-}

-- | /O(n+m)/ The 'count' function returns the number of times the
-- query string appears in the given 'JSString'. An empty query string is
-- invalid, and will cause an error to be raised.
--
-- In (unlikely) bad cases, this function's time complexity degrades
-- towards /O(n*m)/.
count :: JSString -> JSString -> Int
count pat src
  | null pat  = emptyError "count"
  | otherwise = I# (js_count pat src)
{-# INLINE [1] count #-}

--  RULES
-- "JSSTRING count/singleton -> countChar" [~1] forall c t.
--    count (singleton c) t = countChar c t
--

-- | /O(n)/ The 'countChar' function returns the number of times the
-- query element appears in the given 'JSString'. Subject to fusion.
countChar :: Char -> JSString -> Int
countChar c t = S.countChar c (stream t)
{-# INLINE countChar #-}

-------------------------------------------------------------------------------
-- * Zipping

-- | /O(n)/ 'zip' takes two 'JSString's and returns a list of
-- corresponding pairs of bytes. If one input 'JSString' is short,
-- excess elements of the longer 'JSString' are discarded. This is
-- equivalent to a pair of 'unpack' operations.
zip :: JSString -> JSString -> [(Char,Char)]
zip a b = S.unstreamList $ S.zipWith (,) (stream a) (stream b)
{-# INLINE zip #-}

-- | /O(n)/ 'zipWith' generalises 'zip' by zipping with the function
-- given as the first argument, instead of a tupling function.
-- Performs replacement on invalid scalar values.
zipWith :: (Char -> Char -> Char) -> JSString -> JSString -> JSString
zipWith f t1 t2 = unstream (S.zipWith g (stream t1) (stream t2))
    where g a b = safe (f a b)
{-# INLINE zipWith #-}

-- | /O(n)/ Breaks a 'JSString' up into a list of words, delimited by 'Char's
-- representing white space.
words :: JSString -> [JSString]
words x = loop 0# -- js_words x {- t@(Text arr off len) = loop 0 0
  where
    loop i = case js_words1 i x of
                (# n, w #) -> case n of
                                -1# -> []
                                _   -> w : loop n
{-# INLINE words #-}

-- fixme: strict words' that allocates the whole list in one go
words' :: JSString -> [JSString]
words' x = unsafeCoerce (js_words x)
{-# INLINE words' #-}

-- | /O(n)/ Breaks a 'JSString' up into a list of 'JSString's at
-- newline 'Char's. The resulting strings do not contain newlines.
lines :: JSString -> [JSString]
lines ps = loop 0#
  where
    loop i = case js_lines1 i ps of
               (# n, l #) -> case n of
                               -1# -> []
                               _   -> l : loop n
{-# INLINE lines #-}

lines' :: JSString -> [JSString]
lines' ps = unsafeCoerce (js_lines ps)
{-# INLINE lines' #-}

{-
-- | /O(n)/ Portably breaks a 'JSString' up into a list of 'JSString's at line
-- boundaries.
--
-- A line boundary is considered to be either a line feed, a carriage
-- return immediately followed by a line feed, or a carriage return.
-- This accounts for both Unix and Windows line ending conventions,
-- and for the old convention used on Mac OS 9 and earlier.
lines' :: Text -> [Text]
lines' ps | null ps   = []
          | otherwise = h : case uncons t of
                              Nothing -> []
                              Just (c,t')
                                  | c == '\n' -> lines t'
                                  | c == '\r' -> case uncons t' of
                                                   Just ('\n',t'') -> lines t''
                                                   _               -> lines t'
    where (h,t)    = span notEOL ps
          notEOL c = c /= '\n' && c /= '\r'

-}

-- | /O(n)/ Joins lines, after appending a terminating newline to
-- each.
unlines :: [JSString] -> JSString
unlines xs = rnf xs `seq` js_unlines (unsafeCoerce xs)
{-# INLINE unlines #-}

-- | /O(n)/ Joins words using single space characters.
unwords :: [JSString] -> JSString
unwords xs = rnf xs `seq` js_unwords (unsafeCoerce xs)
{-# INLINE unwords #-}

-- | /O(n)/ The 'isPrefixOf' function takes two 'JSString's and returns
-- 'True' iff the first is a prefix of the second.  Subject to fusion.
isPrefixOf :: JSString -> JSString -> Bool
isPrefixOf x y = js_isPrefixOf x y
{-# INLINE [1] isPrefixOf #-}

{-# RULES
"JSSTRING isPrefixOf -> fused" [~1] forall x y.
    isPrefixOf x y = S.isPrefixOf (stream x) (stream y)
"JSSTRING isPrefixOf -> unfused" [1] forall x y.
     S.isPrefixOf (stream x) (stream y) = isPrefixOf x y
  #-}

-- | /O(n)/ The 'isSuffixOf' function takes two 'JSString's and returns
-- 'True' iff the first is a suffix of the second.
isSuffixOf :: JSString -> JSString -> Bool
isSuffixOf x y = js_isSuffixOf x y
{-# INLINE isSuffixOf #-}

-- | The 'isInfixOf' function takes two 'JSString's and returns
-- 'True' iff the first is contained, wholly and intact, anywhere
-- within the second.
--
-- Complexity depends on how the JavaScript engine implements
-- String.prototype.find.
isInfixOf :: JSString -> JSString -> Bool
isInfixOf needle haystack = js_isInfixOf needle haystack
{-# INLINE [1] isInfixOf #-}

{-# RULES
"JSSTRING isInfixOf/singleton -> S.elem/S.stream" [~1] forall n h.
    isInfixOf (singleton n) h = S.elem n (S.stream h)
  #-}

-------------------------------------------------------------------------------
-- * View patterns

-- | /O(n)/ Return the suffix of the second string if its prefix
-- matches the entire first string.
--
-- Examples:
--
-- >>> stripPrefix "foo" "foobar"
-- Just "bar"
--
-- >>> stripPrefix ""    "baz"
-- Just "baz"
--
-- >>> stripPrefix "foo" "quux"
-- Nothing
--
-- This is particularly useful with the @ViewPatterns@ extension to
-- GHC, as follows:
--
-- > {-# LANGUAGE ViewPatterns #-}
-- > import Data.Text as T
-- >
-- > fnordLength :: JSString -> Int
-- > fnordLength (stripPrefix "fnord" -> Just suf) = T.length suf
-- > fnordLength _                                 = -1
stripPrefix :: JSString -> JSString -> Maybe JSString
stripPrefix x y = unsafeCoerce (js_stripPrefix x y)
{-# INLINE stripPrefix #-}

-- | /O(n)/ Find the longest non-empty common prefix of two strings
-- and return it, along with the suffixes of each string at which they
-- no longer match.
--
-- If the strings do not have a common prefix or either one is empty,
-- this function returns 'Nothing'.
--
-- Examples:
--
-- >>> commonPrefixes "foobar" "fooquux"
-- Just ("foo","bar","quux")
--
-- >>> commonPrefixes "veeble" "fetzer"
-- Nothing
--
-- >>> commonPrefixes "" "baz"
-- Nothing
commonPrefixes :: JSString -> JSString -> Maybe (JSString,JSString,JSString)
commonPrefixes x y = unsafeCoerce (js_commonPrefixes x y)
{-# INLINE commonPrefixes #-}

-- | /O(n)/ Return the prefix of the second string if its suffix
-- matches the entire first string.
--
-- Examples:
--
-- >>> stripSuffix "bar" "foobar"
-- Just "foo"
--
-- >>> stripSuffix ""    "baz"
-- Just "baz"
--
-- >>> stripSuffix "foo" "quux"
-- Nothing
--
-- This is particularly useful with the @ViewPatterns@ extension to
-- GHC, as follows:
--
-- > {-# LANGUAGE ViewPatterns #-}
-- > import Data.Text as T
-- >
-- > quuxLength :: Text -> Int
-- > quuxLength (stripSuffix "quux" -> Just pre) = T.length pre
-- > quuxLength _                                = -1
stripSuffix :: JSString -> JSString -> Maybe JSString
stripSuffix x y = unsafeCoerce (js_stripSuffix x y)
{-# INLINE stripSuffix #-}

-- | Add a list of non-negative numbers.  Errors out on overflow.
sumP :: String -> [Int] -> Int
sumP fun = go 0
  where go !a (x:xs)
            | ax >= 0   = go ax xs
            | otherwise = overflowError fun
          where ax = a + x
        go a  _         = a

emptyError :: String -> a
emptyError fun = P.error $ "Data.JSString." ++ fun ++ ": empty input"

overflowError :: String -> a
overflowError fun = P.error $ "Data.JSString." ++ fun ++ ": size overflow"

charWidth :: Int# -> Int#
charWidth cp | isTrue# (cp >=# 0x10000#) = 2#
             | otherwise                 = 1#
{-# INLINE charWidth #-}

-- -----------------------------------------------------------------------------

foreign import javascript unsafe
  "h$jsstringPack($1)" js_pack :: Exts.Any -> JSString
foreign import javascript unsafe
  "$1===''" js_null :: JSString -> Bool
foreign import javascript unsafe
  "$1===null" js_isNull :: JSVal -> Bool
foreign import javascript unsafe
  "$1===$2" js_eq :: JSString -> JSString -> Bool
foreign import javascript unsafe
--  "h$jsstringAppend" js_append :: JSString -> JSString -> JSString -- debug
  "$1+$2" js_append :: JSString -> JSString -> JSString
foreign import javascript unsafe
  "h$jsstringCompare" js_compare :: JSString -> JSString -> Int#
--  "($1<$2)?-1:(($1>$2)?1:0)" js_compare :: JSString -> JSString -> Int#
foreign import javascript unsafe
  "h$jsstringSingleton" js_singleton :: Char -> JSString
foreign import javascript unsafe
  "h$jsstringUnpack" js_unpack :: JSString -> Exts.Any -- String
foreign import javascript unsafe
  "h$jsstringCons" js_cons :: Char -> JSString -> JSString
foreign import javascript unsafe
  "h$jsstringSnoc" js_snoc :: JSString -> Char -> JSString
foreign import javascript unsafe
  "h$jsstringUncons" js_uncons :: JSString -> (# Int#, JSString #)
foreign import javascript unsafe
  "h$jsstringUnsnoc" js_unsnoc :: JSString -> (# Int#, JSString #)
foreign import javascript unsafe
  "$3.substr($1,$2)" js_substr :: Int# -> Int# -> JSString -> JSString
foreign import javascript unsafe
  "$2.substr($1)" js_substr1 :: Int# -> JSString -> JSString
foreign import javascript unsafe
  "$3.substring($1,$2)" js_substring :: Int# -> Int# -> JSString -> JSString
foreign import javascript unsafe
  "$1.length" js_length :: JSString -> Int#
foreign import javascript unsafe
  "(($2.charCodeAt($1)|1023)===0xDBFF)?2:1" js_charWidthAt
  :: Int# -> JSString -> Int#
foreign import javascript unsafe
  "h$jsstringIndex" js_index :: Int# -> JSString -> Int#
foreign import javascript unsafe
  "h$jsstringIndexR" js_indexR :: Int# -> JSString -> Int#
foreign import javascript unsafe
  "h$jsstringUncheckedIndex" js_uncheckedIndex :: Int# -> JSString -> Int#
foreign import javascript unsafe
  "h$jsstringIndexR" js_uncheckedIndexR :: Int# -> JSString -> Int#

-- js_head and js_last return -1 for empty string
foreign import javascript unsafe
  "h$jsstringHead" js_head :: JSString -> Int#
foreign import javascript unsafe
  "h$jsstringLast" js_last :: JSString -> Int#

foreign import javascript unsafe
  "h$jsstringInit" js_init :: JSString -> JSVal -- null for empty string
foreign import javascript unsafe
  "h$jsstringTail" js_tail :: JSString -> JSVal -- null for empty string
foreign import javascript unsafe
  "h$jsstringReverse" js_reverse :: JSString -> JSString
foreign import javascript unsafe
  "h$jsstringGroup"  js_group :: JSString -> Exts.Any {- [JSString] -}
--foreign import javascript unsafe
--  "h$jsstringGroup1" js_group1
--  :: Int# -> Bool -> JSString -> (# Int#, JSString #)
foreign import javascript unsafe
   "h$jsstringConcat" js_concat :: Exts.Any {- [JSString] -} -> JSString
-- debug this below!
foreign import javascript unsafe
   "h$jsstringReplace" js_replace :: JSString -> JSString -> JSString -> JSString
foreign import javascript unsafe
  "h$jsstringCount" js_count :: JSString -> JSString -> Int#
foreign import javascript unsafe
  "h$jsstringWords1" js_words1 :: Int# -> JSString -> (# Int#, JSString #)
foreign import javascript unsafe
  "h$jsstringWords" js_words :: JSString -> Exts.Any -- [JSString]
foreign import javascript unsafe
  "h$jsstringLines1" js_lines1 :: Int# -> JSString -> (# Int#, JSString #)
foreign import javascript unsafe
  "h$jsstringLines" js_lines :: JSString -> Exts.Any -- [JSString]
foreign import javascript unsafe
  "h$jsstringUnlines" js_unlines :: Exts.Any {- [JSString] -} -> JSString
foreign import javascript unsafe
  "h$jsstringUnwords" js_unwords :: Exts.Any {- [JSString] -} -> JSString
foreign import javascript unsafe
  "h$jsstringIsPrefixOf" js_isPrefixOf :: JSString -> JSString -> Bool
foreign import javascript unsafe
  "h$jsstringIsSuffixOf" js_isSuffixOf :: JSString -> JSString -> Bool
foreign import javascript unsafe
  "h$jsstringIsInfixOf" js_isInfixOf :: JSString -> JSString -> Bool
foreign import javascript unsafe
  "h$jsstringStripPrefix" js_stripPrefix
  :: JSString -> JSString -> Exts.Any -- Maybe JSString
foreign import javascript unsafe
  "h$jsstringStripSuffix" js_stripSuffix
  :: JSString -> JSString -> Exts.Any -- Maybe JSString
foreign import javascript unsafe
  "h$jsstringCommonPrefixes" js_commonPrefixes
  :: JSString -> JSString -> Exts.Any -- Maybe (JSString, JSString, JSString)
foreign import javascript unsafe
  "h$jsstringChunksOf" js_chunksOf
  :: Int# -> JSString -> Exts.Any -- [JSString]
foreign import javascript unsafe
  "h$jsstringChunksOf1" js_chunksOf1
  :: Int# -> Int# -> JSString -> (# Int#, JSString #)
foreign import javascript unsafe
  "h$jsstringSplitAt" js_splitAt
  :: Int# -> JSString -> (# JSString, JSString #)
foreign import javascript unsafe
  "h$jsstringSplitOn" js_splitOn
  :: JSString -> JSString -> Exts.Any -- [JSString]
foreign import javascript unsafe
  "h$jsstringSplitOn1" js_splitOn1
  :: Int# -> JSString -> JSString -> (# Int#, JSString #)
foreign import javascript unsafe
  "h$jsstringBreakOn" js_breakOn
  :: JSString -> JSString -> (# JSString, JSString #)
foreign import javascript unsafe
  "h$jsstringBreakOnEnd" js_breakOnEnd
  :: JSString -> JSString -> (# JSString, JSString #)
foreign import javascript unsafe
  "h$jsstringBreakOnAll" js_breakOnAll
  :: JSString -> JSString -> Exts.Any -- [(JSString, JSString)]
foreign import javascript unsafe
  "h$jsstringBreakOnAll1" js_breakOnAll1
  :: Int# -> JSString -> JSString -> (# Int#, JSString, JSString #)
foreign import javascript unsafe
  "h$jsstringDrop" js_drop :: Int# -> JSString -> JSString
foreign import javascript unsafe
  "h$jsstringDropEnd" js_dropEnd :: Int -> JSString -> JSString
foreign import javascript unsafe
  "h$jsstringTake" js_take :: Int# -> JSString -> JSString
foreign import javascript unsafe
  "h$jsstringTakeEnd" js_takeEnd :: Int# -> JSString -> JSString
foreign import javascript unsafe
  "h$jsstringReplicate" js_replicate :: Int# -> JSString -> JSString
foreign import javascript unsafe
  "h$jsstringReplicateChar" js_replicateChar :: Int -> Char -> JSString
foreign import javascript unsafe
  "var l=$1.length; $r=l==1||(l==2&&($1.charCodeAt(0)|1023)==0xDFFF);"
  js_isSingleton :: JSString -> Bool
foreign import javascript unsafe
  "h$jsstringIntersperse"
  js_intersperse :: Char -> JSString -> JSString
foreign import javascript unsafe
  "h$jsstringIntercalate"
  js_intercalate :: JSString -> Exts.Any {- [JSString] -} -> JSString
foreign import javascript unsafe
  "$1.toUpperCase()" js_toUpper :: JSString -> JSString
foreign import javascript unsafe
  "$1.toLowerCase()" js_toLower :: JSString -> JSString
