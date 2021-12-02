{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TypeFamilies      #-}
module PlutusCore.Parser.Lexer where

import PlutusCore qualified as PLC
import PlutusCore.Lexer.Type as LT
import PlutusCore.ParserCommon as PLC (Parser)
import PlutusPrelude (NonEmpty ((:|)), Pretty (pretty), Render (render))

import Data.List qualified as DL
import Data.List.NonEmpty qualified as NE
import Data.Proxy (Proxy (..))
import Data.Set qualified as Set
import PlutusCore.Lexer.Type (Keyword (KwIFix, KwLam))
import Text.Megaparsec
import Text.Megaparsec.Byte
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

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

{- Note [Precedence of regular expression matches]
For reference, Section 3.2.2 of the Alex manual says "When the input stream
matches more than one rule, the rule which matches the longest prefix of the
input stream wins. If there are still several rules which match an equal
number of characters, then the rule which appears earliest in the file wins."
-}

pKeyword :: Parser Keyword
pScheme = choice
  [ KwAbs <$ string "abs"
  , KwLam <$ string "lam"
  , KwIFix <$ string "ifix"
  , KwFun <$ string "fun"
  , KwAll <$ string "all"
  , KwType <$ string "type"
  , KwProgram <$ string "program"
  , KwCon <$ string "con"
  , KwIWrap <$ string "iwrap"
  , KwBuiltin <$ string "builtin"
  , KwUnwrap <$ string "unwrap"
  , KwError <$ string "error"
  , KwForce <$ string "force"
  , KwDelay <$ string "delay"]


data WithPos a = WithPos
  { startPos    :: SourcePos
  , endPos      :: SourcePos
  , tokenLength :: Int
  , tokenVal    :: a
  } deriving (Eq, Ord, Show)

data TkStream = TkStream
  { tkStreamInput :: String -- for showing offending lines
  , unTkStream    :: [WithPos LT.Token]
  }

-- data KwStream = KwStream
--   { kwStreamInput :: String
--   , unKwStream :: [WithPos Keyword ]
--   }

instance Stream TkStream where
  type Token  TkStream = WithPos LT.Token
  type Tokens TkStream = [WithPos LT.Token]

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

showToken :: LT.Token -> String
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

type Parser = Parsec (PLC.ParseError SourcePos) TkStream

liftToken :: LT.Token -> WithPos LT.Token
liftToken = WithPos pos pos 0
  where
    pos = initialPos ""

pToken :: LT.Token -> Parser LT.Token
pToken c = token test (Set.singleton . Tokens . nes . liftToken $ c)
  where
    test (WithPos _ _ _ x) =
      if x == c
        then Just x
        else Nothing
    nes x = x :| []
