{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TypeFamilies      #-}
module PlutusCore.Lexer.Lexer where

import           PlutusCore.Lexer      (AlexPosn)
import           PlutusCore.Lexer.Type as L (Token)
import           PlutusPrelude         (NonEmpty ((:|)), Pretty (pretty), Render (render))

import qualified Data.List             as DL
import qualified Data.List.NonEmpty    as NE
import           Data.Proxy            (Proxy (..))
import qualified Data.Set              as Set
import           Data.Void             (Void)
import           Text.Megaparsec

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
