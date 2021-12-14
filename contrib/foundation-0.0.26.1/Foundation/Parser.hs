-- |
-- Module      : Foundation.Parser
-- License     : BSD-style
-- Maintainer  : Haskell Foundation
-- Stability   : experimental
-- Portability : portable
--
-- The current implementation is mainly, if not copy/pasted, inspired from
-- `memory`'s Parser.
--
-- Foundation Parser makes use of the Foundation's @Collection@ and
-- @Sequential@ classes to allow you to define generic parsers over any
-- @Sequential@ of inpu.
--
-- This way you can easily implements parsers over @LString@, @String@.
--
--
-- > flip parseOnly "my.email@address.com" $ do
-- >    EmailAddress
-- >      <$> (takeWhile ((/=) '@' <*  element '@')
-- >      <*> takeAll
--

{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Foundation.Parser
    ( Parser
    , parse
    , parseFeed
    , parseOnly
    , -- * Result
      Result(..)
    , ParseError(..)
    , reportError

    , -- * Parser source
      ParserSource(..)

    , -- * combinator
      peek
    , element
    , anyElement
    , elements
    , string

    , satisfy
    , satisfy_
    , take
    , takeWhile
    , takeAll

    , skip
    , skipWhile
    , skipAll

    , (<|>)
    , many
    , some
    , optional
    , repeat, Condition(..), And(..)
    ) where

import           Control.Applicative (Alternative, empty, (<|>), many, some, optional)
import           Control.Monad (MonadPlus, mzero, mplus)

import           Basement.Compat.Base
import           Basement.Types.OffsetSize
import           Foundation.Numerical
import           Foundation.Collection hiding (take, takeWhile)
import qualified Foundation.Collection as C
import           Foundation.String

-- Error handling -------------------------------------------------------------

-- | common parser error definition
data ParseError input
    = NotEnough (CountOf (Element input))
        -- ^ meaning the parser was short of @CountOf@ @Element@ of `input`.
    | NotEnoughParseOnly
        -- ^ The parser needed more data, only when using @parseOnly@
    | ExpectedElement (Element input) (Element input)
        -- ^ when using @element@
    | Expected (Chunk input) (Chunk input)
        -- ^ when using @elements@ or @string@
    | Satisfy (Maybe String)
        -- ^ the @satisfy@ or @satisfy_@ function failed,
  deriving (Typeable)
instance (Typeable input, Show input) => Exception (ParseError input)

instance Show input => Show (ParseError input) where
    show (NotEnough (CountOf sz)) = "NotEnough: missing " <> show sz <> " element(s)"
    show NotEnoughParseOnly    = "NotEnough, parse only"
    show (ExpectedElement _ _) = "Expected _ but received _"
    show (Expected _ _)        = "Expected _ but received _"
    show (Satisfy Nothing)     = "Satisfy"
    show (Satisfy (Just s))    = "Satisfy: " <> toList s

instance {-# OVERLAPPING #-} Show (ParseError String) where
    show (NotEnough (CountOf sz)) = "NotEnough: missing " <> show sz <> " element(s)"
    show NotEnoughParseOnly    = "NotEnough, parse only"
    show (ExpectedElement a b) = "Expected "<>show a<>" but received " <> show b
    show (Expected a b)        = "Expected "<>show a<>" but received " <> show b
    show (Satisfy Nothing)     = "Satisfy"
    show (Satisfy (Just s))    = "Satisfy: " <> toList s

-- Results --------------------------------------------------------------------

-- | result of executing the `parser` over the given `input`
data Result input result
    = ParseFailed (ParseError input)
        -- ^ the parser failed with the given @ParserError@
    | ParseOk     (Chunk input) result
        -- ^ the parser complete successfuly with the remaining @Chunk@
    | ParseMore   (Chunk input -> Result input result)
        -- ^ the parser needs more input, pass an empty @Chunk@ or @mempty@
        -- to tell the parser you don't have anymore inputs.

instance (Show k, Show input) => Show (Result input k) where
    show (ParseFailed err) = "Parser failed: " <> show err
    show (ParseOk _ k) = "Parser succeed: " <> show k
    show (ParseMore _) = "Parser incomplete: need more"
instance Functor (Result input) where
    fmap f r = case r of
        ParseFailed err -> ParseFailed err
        ParseOk rest a  -> ParseOk rest (f a)
        ParseMore more -> ParseMore (fmap f . more)

-- Parser Source --------------------------------------------------------------

class (Sequential input, IndexedCollection input) => ParserSource input where
    type Chunk input

    nullChunk :: input -> Chunk input -> Bool

    appendChunk :: input -> Chunk input -> input

    subChunk :: input -> Offset (Element input) -> CountOf (Element input) -> Chunk input

    spanChunk :: input -> Offset (Element input) -> (Element input -> Bool) -> (Chunk input, Offset (Element input))

endOfParserSource :: ParserSource input => input -> Offset (Element input) -> Bool
endOfParserSource l off = off .==# length l
{-# INLINE endOfParserSource #-}

-- Parser ---------------------------------------------------------------------

data NoMore = More | NoMore
  deriving (Show, Eq)

type Failure input         result = input -> Offset (Element input) -> NoMore -> ParseError input -> Result input result

type Success input result' result = input -> Offset (Element input) -> NoMore -> result'          -> Result input result

-- | Foundation's @Parser@ monad.
--
-- Its implementation is based on the parser in `memory`.
newtype Parser input result = Parser
    { runParser :: forall result'
                 . input -> Offset (Element input) -> NoMore
                -> Failure input        result'
                -> Success input result result'
                -> Result input result'
    }

instance Functor (Parser input) where
    fmap f fa = Parser $ \buf off nm err ok ->
        runParser fa buf off nm err $ \buf' off' nm' a -> ok buf' off' nm' (f a)
    {-# INLINE fmap #-}

instance ParserSource input => Applicative (Parser input) where
    pure a = Parser $ \buf off nm _ ok -> ok buf off nm a
    {-# INLINE pure #-}
    fab <*> fa = Parser $ \buf0 off0 nm0 err ok ->
        runParser  fab buf0 off0 nm0 err $ \buf1 off1 nm1 ab ->
        runParser_ fa  buf1 off1 nm1 err $ \buf2 off2 nm2 -> ok buf2 off2 nm2 . ab
    {-# INLINE (<*>) #-}

instance ParserSource input => Monad (Parser input) where
    return = pure
    {-# INLINE return #-}
    m >>= k       = Parser $ \buf off nm err ok ->
        runParser  m     buf  off  nm  err $ \buf' off' nm' a ->
        runParser_ (k a) buf' off' nm' err ok
    {-# INLINE (>>=) #-}

instance ParserSource input => MonadPlus (Parser input) where
    mzero = error "Foundation.Parser.Internal.MonadPlus.mzero"
    mplus f g = Parser $ \buf off nm err ok ->
        runParser f buf off nm (\buf' _ nm' _ -> runParser g buf' off nm' err ok) ok
    {-# INLINE mplus #-}
instance ParserSource input => Alternative (Parser input) where
    empty = error "Foundation.Parser.Internal.Alternative.empty"
    (<|>) = mplus
    {-# INLINE (<|>) #-}

runParser_ :: ParserSource input
           => Parser input result
           -> input
           -> Offset (Element input)
           -> NoMore
           -> Failure input        result'
           -> Success input result result'
           -> Result input         result'
runParser_ parser buf off NoMore err ok = runParser parser buf off NoMore err ok
runParser_ parser buf off nm     err ok
    | endOfParserSource buf off = ParseMore $ \chunk ->
        if nullChunk buf chunk
            then runParser parser buf off NoMore err ok
            else runParser parser (appendChunk buf chunk) off nm err ok
    | otherwise = runParser parser buf                    off nm err ok
{-# INLINE runParser_ #-}

-- | Run a parser on an @initial input.
--
-- If the Parser need more data than available, the @feeder function
-- is automatically called and fed to the More continuation.
parseFeed :: (ParserSource input, Monad m)
          => m (Chunk input)
          -> Parser input a
          -> input
          -> m (Result input a)
parseFeed feeder p initial = loop $ parse p initial
  where loop (ParseMore k) = feeder >>= (loop . k)
        loop r             = return r

-- | Run a Parser on a ByteString and return a 'Result'
parse :: ParserSource input
      => Parser input a -> input -> Result input a
parse p s = runParser p s 0 More failure success

failure :: input -> Offset (Element input) -> NoMore -> ParseError input -> Result input r
failure _ _ _ = ParseFailed
{-# INLINE failure #-}

success :: ParserSource input => input -> Offset (Element input) -> NoMore -> r -> Result input r
success buf off _ = ParseOk rest
  where
    !rest = subChunk buf off (length buf `sizeSub` offsetAsSize off)
{-# INLINE success #-}

-- | parse only the given input
--
-- The left-over `Element input` will be ignored, if the parser call for more
-- data it will be continuously fed with `Nothing` (up to 256 iterations).
--
parseOnly :: (ParserSource input, Monoid (Chunk input))
          => Parser input a
          -> input
          -> Either (ParseError input) a
parseOnly p i = case runParser p i 0 NoMore failure success of
    ParseFailed err  -> Left err
    ParseOk     _ r  -> Right r
    ParseMore   _    -> Left NotEnoughParseOnly

-- ------------------------------------------------------------------------- --
--                              String Parser                                --
-- ------------------------------------------------------------------------- --

instance ParserSource String where
    type Chunk String = String
    nullChunk _ = null
    {-# INLINE nullChunk #-}
    appendChunk = mappend
    {-# INLINE appendChunk #-}
    subChunk c off sz = C.take sz $ C.drop (offsetAsSize off) c
    {-# INLINE subChunk #-}
    spanChunk buf off predicate =
        let c      = C.drop (offsetAsSize off) buf
            (t, _) = C.span predicate c
          in (t, off `offsetPlusE` length t)
    {-# INLINE spanChunk #-}

instance ParserSource [a] where
    type Chunk [a] = [a]
    nullChunk _ = null
    {-# INLINE nullChunk #-}
    appendChunk = mappend
    {-# INLINE appendChunk #-}
    subChunk c off sz = C.take sz $ C.drop (offsetAsSize off) c
    {-# INLINE subChunk #-}
    spanChunk buf off predicate =
        let c      = C.drop (offsetAsSize off) buf
            (t, _) = C.span predicate c
          in (t, off `offsetPlusE` length t)
    {-# INLINE spanChunk #-}

-- ------------------------------------------------------------------------- --
--                          Helpers                                          --
-- ------------------------------------------------------------------------- --

-- | helper function to report error when writing parsers
--
-- This way we can provide more detailed error when building custom
-- parsers and still avoid to use the naughty _fail_.
--
-- @
-- myParser :: Parser input Int
-- myParser = reportError $ Satisfy (Just "this function is not implemented...")
-- @
--
reportError :: ParseError input -> Parser input a
reportError pe = Parser $ \buf off nm err _ -> err buf off nm pe

-- | Get the next `Element input` from the parser
anyElement :: ParserSource input => Parser input (Element input)
anyElement = Parser $ \buf off nm err ok ->
    case buf ! off of
        Nothing -> err buf off        nm $ NotEnough 1
        Just x  -> ok  buf (succ off) nm x
{-# INLINE anyElement #-}

-- | peek the first element from the input source without consuming it
--
-- Returns 'Nothing' if there is no more input to parse.
--
peek :: ParserSource input => Parser input (Maybe (Element input))
peek = Parser $ \buf off nm err ok ->
    case buf ! off of
        Nothing -> runParser_ peekOnly buf off nm err ok
        Just x  -> ok buf off nm (Just x)
  where
    peekOnly = Parser $ \buf off nm _ ok ->
        ok buf off nm (buf ! off)

element :: ( ParserSource input
           , Eq (Element input)
           , Element input ~ Element (Chunk input)
           )
        => Element input
        -> Parser input ()
element expectedElement = Parser $ \buf off nm err ok ->
    case buf ! off of
        Nothing -> err buf off nm $ NotEnough 1
        Just x | expectedElement == x -> ok  buf (succ off) nm ()
               | otherwise            -> err buf off nm $ ExpectedElement expectedElement x
{-# INLINE element #-}

elements :: ( ParserSource input, Sequential (Chunk input)
            , Element (Chunk input) ~ Element input
            , Eq (Chunk input)
            )
         => Chunk input -> Parser input ()
elements = consumeEq
  where
    consumeEq :: ( ParserSource input
                 , Sequential (Chunk input)
                 , Element (Chunk input) ~ Element input
                 , Eq (Chunk input)
                 )
              => Chunk input -> Parser input ()
    consumeEq expected = Parser $ \buf off nm err ok ->
      if endOfParserSource buf off
        then
          err buf off nm $ NotEnough lenE
        else
          let !lenI = sizeAsOffset (length buf) - off
           in if lenI >= lenE
             then
              let a = subChunk buf off lenE
               in if a == expected
                    then ok buf (off + sizeAsOffset lenE) nm ()
                    else err buf off nm $ Expected expected a
             else
              let a = subChunk buf off lenI
                  (e', r) = splitAt lenI expected
               in if a == e'
                    then runParser_ (consumeEq r) buf (off + sizeAsOffset lenI) nm err ok
                    else err buf off nm $ Expected e' a
      where
        !lenE = length expected
    {-# NOINLINE consumeEq #-}
{-# INLINE elements #-}

-- | take one element if satisfy the given predicate
satisfy :: ParserSource input => Maybe String -> (Element input -> Bool) -> Parser input (Element input)
satisfy desc predicate = Parser $ \buf off nm err ok ->
    case buf ! off of
        Nothing -> err buf off nm $ NotEnough 1
        Just x | predicate x -> ok  buf (succ off) nm x
               | otherwise   -> err buf off nm $ Satisfy desc
{-# INLINE satisfy #-}

-- | take one element if satisfy the given predicate
satisfy_ :: ParserSource input => (Element input -> Bool) -> Parser input (Element input)
satisfy_ = satisfy Nothing
{-# INLINE satisfy_ #-}

take :: ( ParserSource input
        , Sequential (Chunk input)
        , Element input ~ Element (Chunk input)
        )
     => CountOf (Element (Chunk input))
     -> Parser input (Chunk input)
take n = Parser $ \buf off nm err ok ->
    let lenI = sizeAsOffset (length buf) - off
     in if endOfParserSource buf off && n > 0
       then err buf off nm $ NotEnough n
       else case n - lenI of
              Just s | s > 0 -> let h = subChunk buf off lenI
                                 in runParser_ (take s) buf (sizeAsOffset lenI) nm err $
                                      \buf' off' nm' t -> ok buf' off' nm' (h <> t)
              _              -> ok buf (off + sizeAsOffset n) nm (subChunk buf off n)

takeWhile :: ( ParserSource input, Sequential (Chunk input)
             )
          => (Element input -> Bool)
          -> Parser input (Chunk input)
takeWhile predicate = Parser $ \buf off nm err ok ->
    if endOfParserSource buf off
      then ok buf off nm mempty
      else let (b1, off') = spanChunk buf off predicate
            in if endOfParserSource buf off'
                  then runParser_ (takeWhile predicate) buf off' nm err
                          $ \buf' off'' nm' b1T -> ok buf' off'' nm' (b1 <> b1T)
                  else ok buf off' nm b1

-- | Take the remaining elements from the current position in the stream
takeAll :: (ParserSource input, Sequential (Chunk input)) => Parser input (Chunk input)
takeAll = getAll >> returnBuffer
  where
    returnBuffer :: ParserSource input => Parser input (Chunk input)
    returnBuffer = Parser $ \buf off nm _ ok ->
        let !lenI = length buf
            !off' = sizeAsOffset lenI
            !sz   = off' - off
         in ok buf off' nm (subChunk buf off sz)
    {-# INLINE returnBuffer #-}

    getAll :: (ParserSource input, Sequential (Chunk input)) => Parser input ()
    getAll = Parser $ \buf off nm err ok ->
      case nm of
        NoMore -> ok buf off nm ()
        More   -> ParseMore $ \nextChunk ->
          if nullChunk buf nextChunk
            then ok buf off NoMore ()
            else runParser getAll (appendChunk buf nextChunk) off nm err ok
    {-# NOINLINE getAll #-}
{-# INLINE takeAll #-}

skip :: ParserSource input => CountOf (Element input) -> Parser input ()
skip n = Parser $ \buf off nm err ok ->
    let lenI = sizeAsOffset (length buf) - off
     in if endOfParserSource buf off && n > 0
       then err buf off nm $ NotEnough n
       else case n - lenI of
              Just s | s > 0 -> runParser_ (skip s) buf (sizeAsOffset lenI) nm err ok
              _              -> ok buf (off + sizeAsOffset n) nm ()

skipWhile :: ( ParserSource input, Sequential (Chunk input)
             )
          => (Element input -> Bool)
          -> Parser input ()
skipWhile predicate = Parser $ \buf off nm err ok ->
    if endOfParserSource buf off
      then ok buf off nm ()
      else let (_, off') = spanChunk buf off predicate
            in if endOfParserSource buf off'
                  then runParser_ (skipWhile predicate) buf off' nm err ok
                  else ok buf off' nm ()

-- | consume every chunk of the stream
--
skipAll :: (ParserSource input, Collection (Chunk input)) => Parser input ()
skipAll = flushAll
  where
    flushAll :: (ParserSource input, Collection (Chunk input)) => Parser input ()
    flushAll = Parser $ \buf off nm err ok ->
        let !off' = sizeAsOffset $ length buf in
        case nm of
            NoMore -> ok buf off' NoMore ()
            More   -> ParseMore $ \nextChunk ->
              if null nextChunk
                then ok buf off' NoMore ()
                else runParser flushAll buf off nm err ok
    {-# NOINLINE flushAll #-}
{-# INLINE skipAll #-}

string :: String -> Parser String ()
string = elements
{-# INLINE string #-}

data Condition = Between !And | Exactly !Word
  deriving (Show, Eq, Typeable)
data And = And !Word !Word
  deriving (Eq, Typeable)
instance Show And where
    show (And a b) = show a <> " and " <> show b

-- | repeat the given parser a given amount of time
--
-- Unlike @some@ or @many@, this operation will bring more precision on how
-- many times you wish a parser to be sequenced.
--
-- ## Repeat @Exactly@ a number of time
--
-- > repeat (Exactly 6) (takeWhile ((/=) ',') <* element ',')
--
-- ## Repeat @Between@ lower `@And@` upper times
--
-- > repeat (Between $ 1 `And` 10) (takeWhile ((/=) ',') <* element ',')
--
repeat :: ParserSource input
       => Condition -> Parser input a -> Parser input [a]
repeat (Exactly n) = repeatE n
repeat (Between a) = repeatA a

repeatE :: (ParserSource input)
        => Word -> Parser input a -> Parser input [a]
repeatE 0 _ = return []
repeatE n p = (:) <$> p <*> repeatE (n-1) p

repeatA :: (ParserSource input)
        => And -> Parser input a -> Parser input [a]
repeatA (And 0 0) _ = return []
repeatA (And 0 n) p = ((:) <$> p <*> repeatA (And 0     (n-1)) p) <|> return []
repeatA (And l u) p =  (:) <$> p <*> repeatA (And (l-1) (u-1)) p
