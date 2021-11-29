{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TypeFamilies      #-}
module PlutusCore.Lexer.Lexer where

import PlutusCore.Lexer (AlexPosn)
import PlutusCore.Lexer.Type as L (Token)
import PlutusPrelude (NonEmpty ((:|)), Pretty (pretty), Render (render))

import Data.List qualified as DL
import Data.List.NonEmpty qualified as NE
import Data.Proxy (Proxy (..))
import Data.Set qualified as Set
import Data.Void (Void)
import Text.Megaparsec

{- Note [Keywords] This version of the lexer relaxes the syntax so that keywords
(con, lam, ...) and built-in names can be re-used as variable names, reducing
the risk of textual source code being unparsable due to illegal names (produced
by a compiler, for example). To achieve this, we use Alex's "start codes" which
allow you to put the lexer into modes in which only certain actions are valid.
In the PLC grammar, keywords like `abs`, `con` and so on can only occur after a
`(`, so when we see one of these we put the lexer into a special mode where
these are interpreted as keywords and converted into elements of the LexKeyword
type; having done this, we return to the initial lexer state, denoted by 0,
where we can use keywords as variable names. A similar strategy is used for
built in type names.  -}

{- Note [Literal Constants]
For literal constants, we accept certain types of character sequences that are
then passed to user-defined parsers which convert them to built-in constants.
Literal constants have to specify the type of the constant, so we have (con
integer 9), (con string "Hello"), and so on.  This allows us to use the same
literal syntax for different types (eg, integer, short, etc) and shift most
of the responsibility for parsing constants out of the lexer and into the
parser (and eventually out of the parser to parsers supplied by the types
themselves).

In the body of a constant we allow:
  * ()
  * Single-quoted possibly empty sequences of printable characters
  * Double-quoted possibly empty sequences of printable characters
  * Unquoted non-empty sequences of printable characters not including '(' or ')',
    and not beginning with a single or double quote.  Spaces are allowed in the
    body of the sequence, but are ignored at the beginning or end.

"Printable" here uses Alex's definition: Unicode code points 32 to 0x10ffff.
This includes spaces but excludes tabs amongst other things.  One can use the
usual escape sequences though, as long as the type-specific parser deals with
them.

These allow us to parse all of the standard types.  We just return all of the
characters in a TkLiteralConst token, not attempting to do things like stripping
off quotes or interpreting escape sequences: it's the responsibility of the
parser for the relevant type to do these things.  Note that 'read' will often do
the right thing.

The final item above even allows the possibility of parsing complex types such as
tuples and lists as long as parentheses are not involved.  For example, (con
tuple <1,2.3,"yes">) and (con intlist [1, 2, -7]) are accepted by the lexer, as
is the somewhat improbable-looking (con intseq 12 4 55 -4).  Comment characters
are also allowed, but are not treated specially.  We don't allow (con )) or (con
tuple (1,2,3)) because it would be difficult for the lexer to decide when it
had reached the end of the literal: consider a tuple containing a quoted string
containing ')', for example.
-}

{- Note [Precedence of regular expression matches]
For reference, Section 3.2.2 of the Alex manual says "When the input stream
matches more than one rule, the rule which matches the longest prefix of the
input stream wins. If there are still several rules which match an equal
number of characters, then the rule which appears earliest in the file wins."
-}


data WithPos a = WithPos
  { startPos    :: SourcePos
  , endPos      :: SourcePos
  , tokenLength :: Int
  , tokenVal    :: a
  } deriving (Eq, Ord, Show)

data TkStream = TkStream
  { tkStreamInput :: String -- for showing offending lines
  , unTkStream    :: [WithPos (L.Token AlexPosn)]
  }

-- data KwStream = KwStream
--   { kwStreamInput :: String
--   , unKwStream :: [WithPos Keyword ]
--   }

instance Stream TkStream where
  type Token  TkStream = WithPos (L.Token AlexPosn)
  type Tokens TkStream = [WithPos (L.Token AlexPosn)]

  tokenToChunk Proxy x = [x]
  tokensToChunk Proxy xs = xs
  chunkToTokens Proxy = id
  chunkLength Proxy = length
  chunkEmpty Proxy = null
  take1_ (TkStream _ []) = Nothing
  take1_ (TkStream str (t:ts)) = Just
    ( t
    , TkStream (drop (tokensLength pxy (t:|[])) str) ts
    )
  takeN_ n (TkStream str s)
    | n <= 0    = Just ([], TkStream str s)
    | null s    = Nothing
    | otherwise =
        let (x, s') = splitAt n s
        in case NE.nonEmpty x of
          Nothing  -> Just (x, TkStream str s')
          Just nex -> Just (x, TkStream (drop (tokensLength pxy nex) str) s')
  takeWhile_ f (TkStream str s) =
    let (x, s') = DL.span f s
    in case NE.nonEmpty x of
      Nothing  -> (x, TkStream str s')
      Just nex -> (x, TkStream (drop (tokensLength pxy nex) str) s')

showToken :: L.Token AlexPosn -> String
showToken = render . pretty

instance VisualStream TkStream where
  showTokens Proxy = unwords
    . NE.toList
    . fmap (showToken . tokenVal)
  tokensLength Proxy xs = sum (tokenLength <$> xs)

instance TraversableStream TkStream where
  reachOffset o PosState {..} =
    ( Just (prefix ++ restOfLine)
    , PosState
        { pstateInput = TkStream
            { tkStreamInput = postStr
            , unTkStream = post
            }
        , pstateOffset = max pstateOffset o
        , pstateSourcePos = newSourcePos
        , pstateTabWidth = pstateTabWidth
        , pstateLinePrefix = prefix
        }
    )
    where
      prefix =
        if sameLine
          then pstateLinePrefix ++ preStr
          else preStr
      sameLine = sourceLine newSourcePos == sourceLine pstateSourcePos
      newSourcePos =
        case post of
          []    -> pstateSourcePos
          (x:_) -> startPos x
      (pre, post) = splitAt (o - pstateOffset) (unTkStream pstateInput)
      (preStr, postStr) = splitAt tokensConsumed (tkStreamInput pstateInput)
      tokensConsumed =
        case NE.nonEmpty pre of
          Nothing    -> 0
          Just nePre -> tokensLength pxy nePre
      restOfLine = takeWhile (/= '\n') postStr

pxy :: Proxy TkStream
pxy = Proxy

type Parser = Parsec Void TkStream

liftToken :: L.Token AlexPosn -> WithPos (L.Token AlexPosn)
liftToken = WithPos pos pos 0
  where
    pos = initialPos ""

pToken :: L.Token AlexPosn -> Parser (L.Token AlexPosn)
pToken c = token test (Set.singleton . Tokens . nes . liftToken $ c)
  where
    test (WithPos _ _ _ x) =
      if x == c
        then Just x
        else Nothing
    nes x = x :| []
