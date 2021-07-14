{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TypeFamilies      #-}
module UntypedPlutusCore.Lexer where

import           PlutusCore.Lexer
import           PlutusCore.Lexer.Type as L (Token)
import           PlutusPrelude         (NonEmpty ((:|)), Pretty (pretty), Render (render))

import qualified Data.List             as DL
import qualified Data.List.NonEmpty    as NE
import           Data.Proxy            (Proxy (..))
import           Text.Megaparsec

data WithPos a = WithPos
  { startPos    :: SourcePos
  , endPos      :: SourcePos
  , tokenLength :: Int
  , tokenVal    :: a
  } deriving (Eq, Ord, Show)

data MyStream = MyStream
  { myStreamInput :: String -- for showing offending lines
  , unMyStream    :: [WithPos (L.Token AlexPosn)]
  }
instance Stream MyStream where
  type Token  MyStream = WithPos (L.Token AlexPosn)
  type Tokens MyStream = [WithPos (L.Token AlexPosn)]

  tokenToChunk Proxy x = [x]
  tokensToChunk Proxy xs = xs
  chunkToTokens Proxy = id
  chunkLength Proxy = length
  chunkEmpty Proxy = null
  take1_ (MyStream _ []) = Nothing
  take1_ (MyStream str (t:ts)) = Just
    ( t
    , MyStream (drop (tokensLength pxy (t:|[])) str) ts
    )
  takeN_ n (MyStream str s)
    | n <= 0    = Just ([], MyStream str s)
    | null s    = Nothing
    | otherwise =
        let (x, s') = splitAt n s
        in case NE.nonEmpty x of
          Nothing  -> Just (x, MyStream str s')
          Just nex -> Just (x, MyStream (drop (tokensLength pxy nex) str) s')
  takeWhile_ f (MyStream str s) =
    let (x, s') = DL.span f s
    in case NE.nonEmpty x of
      Nothing  -> (x, MyStream str s')
      Just nex -> (x, MyStream (drop (tokensLength pxy nex) str) s')

showToken :: L.Token AlexPosn -> String
showToken = render . pretty

instance VisualStream MyStream where
  showTokens Proxy = unwords
    . NE.toList
    . fmap (showToken . tokenVal)
  tokensLength Proxy xs = sum (tokenLength <$> xs)

instance TraversableStream MyStream where
  reachOffset o PosState {..} =
    ( Just (prefix ++ restOfLine)
    , PosState
        { pstateInput = MyStream
            { myStreamInput = postStr
            , unMyStream = post
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
      (pre, post) = splitAt (o - pstateOffset) (unMyStream pstateInput)
      (preStr, postStr) = splitAt tokensConsumed (myStreamInput pstateInput)
      tokensConsumed =
        case NE.nonEmpty pre of
          Nothing    -> 0
          Just nePre -> tokensLength pxy nePre
      restOfLine = takeWhile (/= '\n') postStr

pxy :: Proxy MyStream
pxy = Proxy
