-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.Internal.Text.ParserCombinators.ReadP
-- Copyright   :  (c) The University of Glasgow 2002
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  provisional
-- Portability :  non-portable (local universal quantification)
--
-- This is a library of parser combinators, originally written by Koen Claessen.
-- It parses all alternatives in parallel, so it never keeps hold of
-- the beginning of the input string, a common source of space leaks with
-- other parsers.  The @('+++')@ choice combinator is genuinely commutative;
-- it makes no difference which branch is \"shorter\".

-----------------------------------------------------------------------------

module Text.ParserCombinators.ReadP
  (
  -- * The 'ReadP' type
  ReadP,

  -- * Primitive operations
  get,
  look,
  (+++),
  (<++),
  gather,

  -- * Other operations
  pfail,
  eof,
  satisfy,
  char,
  string,
  munch,
  munch1,
  skipSpaces,
  choice,
  count,
  between,
  option,
  optional,
  many,
  many1,
  skipMany,
  skipMany1,
  sepBy,
  sepBy1,
  endBy,
  endBy1,
  chainr,
  chainl,
  chainl1,
  chainr1,
  manyTill,

  -- * Running a parser
  ReadS,
  readP_to_S,
  readS_to_P,

  -- * Properties
  -- $properties
  )
 where
import Control.Applicative hiding (many, optional)
import Control.Error
import Control.Monad
import Control.Monad.Fail
import Data.Bool
import Data.Char
import Data.Eq
import Data.Function
import Data.Functor
import Data.Int
import Data.List
import Data.List.NonEmpty
import Data.Monoid.Internal
import Data.Num
import Prelude qualified ()
import Primitives

default (Int)

infixr 5 +++, <++

------------------------------------------------------------------------
-- ReadS

-- | A parser for a type @a@, represented as a function that takes a
-- 'String' and returns a list of possible parses as @(a,'String')@ pairs.
--
-- Note that this kind of backtracking parser is very inefficient;
-- reading a large structure may be quite slow (cf 'ReadP').
type ReadS a = String -> [(a,String)]

-- ---------------------------------------------------------------------------
-- The P type
-- is representation type -- should be kept abstract

data P a
  = Get (Char -> P a)
  | Look (String -> P a)
  | Fail
  | Result a (P a)
  | Final (NonEmpty (a,String))
--  deriving Functor -- ^ @since base-4.8.0.0

instance Functor P where
  fmap f (Get g)       = Get (fmap f . g)
  fmap f (Look g)      = Look (fmap f . g)
  fmap _ Fail          = Fail
  fmap f (Result a pa) = Result (f a) (fmap f pa)
  fmap f (Final xs)    = Final (fmap (\ (a, s) -> (f a, s)) xs)

-- Monad, MonadPlus

-- | @since base-4.5.0.0
instance Applicative P where
  pure x = Result x Fail
  (<*>) = ap

-- | @since base-2.01
instance MonadPlus P

-- | @since base-2.01
instance Monad P where
  (Get f)         >>= k = Get (f >=> k)
  (Look f)        >>= k = Look (f >=> k)
  Fail            >>= _ = Fail
  (Result x p)    >>= k = k x <|> (p >>= k)
  (Final (r:|rs)) >>= k = final [ys' | (x,s) <- r:rs, ys' <- run (k x) s]

-- | @since base-4.9.0.0
instance MonadFail P where
  fail _ = Fail

-- | @since base-4.5.0.0
instance Alternative P where
  empty = Fail

  -- most common case: two gets are combined
  Get f1     <|> Get f2     = Get (\c -> f1 c <|> f2 c)

  -- results are delivered as soon as possible
  Result x p <|> q          = Result x (p <|> q)
  p          <|> Result x q = Result x (p <|> q)

  -- fail disappears
  Fail       <|> p          = p
  p          <|> Fail       = p

  -- two finals are combined
  -- final + look becomes one look and one final (=optimization)
  -- final + sthg else becomes one look and one final
  Final r       <|> Final t = Final (r <> t)
  Final (r:|rs) <|> Look f  = Look (\s -> Final (r:|(rs ++ run (f s) s)))
  Final (r:|rs) <|> p       = Look (\s -> Final (r:|(rs ++ run p s)))
  Look f        <|> Final r = Look (\s -> Final (case run (f s) s of
                                []     -> r
                                (x:xs) -> (x:|xs) <> r))
  p             <|> Final r = Look (\s -> Final (case run p s of
                                []     -> r
                                (x:xs) -> (x:|xs) <> r))

  -- two looks are combined (=optimization)
  -- look + sthg else floats upwards
  Look f     <|> Look g     = Look (\s -> f s <|> g s)
  Look f     <|> p          = Look (\s -> f s <|> p)
  p          <|> Look f     = Look (\s -> p <|> f s)

-- ---------------------------------------------------------------------------
-- The ReadP type

newtype ReadP a = R (forall b . (a -> P b) -> P b)

-- | @since base-2.01
instance Functor ReadP where
  fmap h (R f) = R (\k -> f (k . h))

-- | @since base-4.6.0.0
instance Applicative ReadP where
    pure x = R (\k -> k x)
    (<*>) = ap
    -- liftA2 = liftM2

-- | @since base-2.01
instance Monad ReadP where
  R m >>= f = R (\k -> m (\a -> let R m' = f a in m' k))

-- | @since base-4.9.0.0
instance MonadFail ReadP where
  fail _    = R (const Fail)

-- | @since base-4.6.0.0
instance Alternative ReadP where
  empty = pfail
  (<|>) = (+++)

-- | @since base-2.01
instance MonadPlus ReadP

-- ---------------------------------------------------------------------------
-- Operations over P

final :: [(a,String)] -> P a
final []     = Fail
final (r:rs) = Final (r:|rs)

run :: P a -> ReadS a
run (Get f)         (c:s) = run (f c) s
run (Look f)        s     = run (f s) s
run (Result x p)    s     = (x,s) : run p s
run (Final (r:|rs)) _     = r:rs
run _               _     = []

-- ---------------------------------------------------------------------------
-- Operations over ReadP

get :: ReadP Char
-- ^ Consumes and returns the next character.
--   Fails if there is no input left.
get = R Get

look :: ReadP String
-- ^ Look-ahead: returns the part of the input that is left, without
--   consuming it.
look = R Look

pfail :: ReadP a
-- ^ Always fails.
pfail = R (const Fail)

(+++) :: ReadP a -> ReadP a -> ReadP a
-- ^ Symmetric choice.
R f1 +++ R f2 = R (\k -> f1 k <|> f2 k)

(<++) :: forall a . ReadP a -> ReadP a -> ReadP a
-- ^ Local, exclusive, left-biased choice: If left parser
--   locally produces any result at all, then right parser is
--   not used.
(<++) (R f0) q =
  do s <- look
     probe (f0 return) s 0
 where
  probe :: P a -> [Char] -> Int -> ReadP a
  probe (Get f)        (c:s) n = probe (f c) s (n + 1)
  probe (Look f)       s     n = probe (f s) s n
  probe p@(Result _ _) _     n = discard n >> R (p >>=)
  probe (Final r)      _     _ = R (Final r >>=)
  probe _              _     _ = q

  discard 0 = return ()
  discard n = get >> discard (n - 1)

gather :: ReadP a -> ReadP (String, a)
-- ^ Transforms a parser into one that does the same, but
--   in addition returns the exact characters read.
--   IMPORTANT NOTE: 'gather' gives a runtime error if its first argument
--   is built using any occurrences of readS_to_P.
gather (R m)
  = R (\k -> gath id (m (\a -> return (\s -> k (s,a)))))

 where
  gath :: (String -> String) -> P (String -> P b) -> P b
  gath l (Get f)      = Get (\c -> gath (l.(c:)) (f c))
  gath _ Fail         = Fail
  gath l (Look f)     = Look (gath l . f)
  gath l (Result k p) = k (l []) <|> gath l p
  gath _ (Final _)    = errorWithoutStackTrace "do not use readS_to_P in gather!"

-- ---------------------------------------------------------------------------
-- Derived operations

satisfy :: (Char -> Bool) -> ReadP Char
-- ^ Consumes and returns the next character, if it satisfies the
--   specified predicate.
satisfy p = do c <- get; if p c then return c else pfail

char :: Char -> ReadP Char
-- ^ Parses and returns the specified character.
char c = satisfy (c ==)

eof :: ReadP ()
-- ^ Succeeds iff we are at the end of input
eof = do { s <- look
         ; unless (null s) pfail }

string :: String -> ReadP String
-- ^ Parses and returns the specified string.
string this = do s <- look; scan this s
 where
  scan []     _               = return this
  scan (x:xs) (y:ys) | x == y = do _ <- get; scan xs ys
  scan _      _               = pfail

munch :: (Char -> Bool) -> ReadP String
-- ^ Parses the first zero or more characters satisfying the predicate.
--   Always succeeds, exactly once having consumed all the characters
--   Hence NOT the same as (many (satisfy p))
munch p =
  do s <- look
     scan s
 where
  scan (c:cs) | p c = do _ <- get; s <- scan cs; return (c:s)
  scan _            = return (""::String)

munch1 :: (Char -> Bool) -> ReadP String
-- ^ Parses the first one or more characters satisfying the predicate.
--   Fails if none, else succeeds exactly once having consumed all the characters
--   Hence NOT the same as (many1 (satisfy p))
munch1 p =
  do c <- get
     if p c then do s <- munch p; return (c:s)
            else pfail

choice :: [ReadP a] -> ReadP a
-- ^ Combines all parsers in the specified list.
choice []     = pfail
choice [p]    = p
choice (p:ps) = p +++ choice ps

skipSpaces :: ReadP ()
-- ^ Skips all whitespace.
skipSpaces =
  do s <- look
     skip s
 where
  skip (c:s) | isSpace c = do _ <- get; skip s
  skip _                 = return ()

count :: Int -> ReadP a -> ReadP [a]
-- ^ @count n p@ parses @n@ occurrences of @p@ in sequence. A list of
--   results is returned.
count n p = replicateM n p

between :: ReadP open -> ReadP close -> ReadP a -> ReadP a
-- ^ @between open close p@ parses @open@, followed by @p@ and finally
--   @close@. Only the value of @p@ is returned.
between open close p = do _ <- open
                          x <- p
                          _ <- close
                          return x

option :: a -> ReadP a -> ReadP a
-- ^ @option x p@ will either parse @p@ or return @x@ without consuming
--   any input.
option x p = p +++ return x

optional :: ReadP a -> ReadP ()
-- ^ @optional p@ optionally parses @p@ and always returns @()@.
optional p = void p +++ return ()

many :: ReadP a -> ReadP [a]
-- ^ Parses zero or more occurrences of the given parser.
many p = return [] +++ many1 p

many1 :: ReadP a -> ReadP [a]
-- ^ Parses one or more occurrences of the given parser.
many1 p = liftM2 (:) p (many p)

skipMany :: ReadP a -> ReadP ()
-- ^ Like 'many', but discards the result.
skipMany p = void (many p)

skipMany1 :: ReadP a -> ReadP ()
-- ^ Like 'many1', but discards the result.
skipMany1 p = p >> skipMany p

sepBy :: ReadP a -> ReadP sep -> ReadP [a]
-- ^ @sepBy p sep@ parses zero or more occurrences of @p@, separated by @sep@.
--   Returns a list of values returned by @p@.
sepBy p sep = sepBy1 p sep +++ return []

sepBy1 :: ReadP a -> ReadP sep -> ReadP [a]
-- ^ @sepBy1 p sep@ parses one or more occurrences of @p@, separated by @sep@.
--   Returns a list of values returned by @p@.
sepBy1 p sep = liftM2 (:) p (many (sep >> p))

endBy :: ReadP a -> ReadP sep -> ReadP [a]
-- ^ @endBy p sep@ parses zero or more occurrences of @p@, separated and ended
--   by @sep@.
endBy p sep = many (do x <- p ; _ <- sep ; return x)

endBy1 :: ReadP a -> ReadP sep -> ReadP [a]
-- ^ @endBy p sep@ parses one or more occurrences of @p@, separated and ended
--   by @sep@.
endBy1 p sep = many1 (do x <- p ; _ <- sep ; return x)

chainr :: ReadP a -> ReadP (a -> a -> a) -> a -> ReadP a
-- ^ @chainr p op x@ parses zero or more occurrences of @p@, separated by @op@.
--   Returns a value produced by a /right/ associative application of all
--   functions returned by @op@. If there are no occurrences of @p@, @x@ is
--   returned.
chainr p op x = chainr1 p op +++ return x

chainl :: ReadP a -> ReadP (a -> a -> a) -> a -> ReadP a
-- ^ @chainl p op x@ parses zero or more occurrences of @p@, separated by @op@.
--   Returns a value produced by a /left/ associative application of all
--   functions returned by @op@. If there are no occurrences of @p@, @x@ is
--   returned.
chainl p op x = chainl1 p op +++ return x

chainr1 :: ReadP a -> ReadP (a -> a -> a) -> ReadP a
-- ^ Like 'chainr', but parses one or more occurrences of @p@.
chainr1 p op = scan
  where scan   = p >>= rest
        rest x = do f <- op
                    y <- scan
                    return (f x y)
                 +++ return x

chainl1 :: ReadP a -> ReadP (a -> a -> a) -> ReadP a
-- ^ Like 'chainl', but parses one or more occurrences of @p@.
chainl1 p op = p >>= rest
  where rest x = do f <- op
                    y <- p
                    rest (f x y)
                 +++ return x

manyTill :: ReadP a -> ReadP end -> ReadP [a]
-- ^ @manyTill p end@ parses zero or more occurrences of @p@, until @end@
--   succeeds. Returns a list of values returned by @p@.
manyTill p end = scan
  where scan = (end >> return []) <++ liftM2 (:) p scan

-- ---------------------------------------------------------------------------
-- Converting between ReadP and Read

readP_to_S :: ReadP a -> ReadS a
-- ^ Converts a parser into a Haskell ReadS-style function.
--   This is the main way in which you can \"run\" a 'ReadP' parser:
--   the expanded type is
-- @ readP_to_S :: ReadP a -> String -> [(a,String)] @
readP_to_S (R f) = run (f return)

readS_to_P :: ReadS a -> ReadP a
-- ^ Converts a Haskell ReadS-style function into a parser.
--   Warning: This introduces local backtracking in the resulting
--   parser, and therefore a possible inefficiency.
readS_to_P r =
  R (\k -> Look (\s -> final [bs'' | (a,s') <- r s, bs'' <- run (k a) s']))
