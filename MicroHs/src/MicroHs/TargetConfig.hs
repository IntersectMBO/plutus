{-# OPTIONS_GHC -Wno-orphans #-}
module MicroHs.TargetConfig(
    Target(..)
  , TTarget(..)
  , parseTargets
  , findTarget
  ) where
import qualified Prelude(); import MHSPrelude hiding(lex)
import Data.List
import Text.ParserComb
import MicroHs.Ident
import MicroHs.Lex

{- File Format
[target_name]
key = "value"
...

[next_target]
key = ...
-}

data Target = Target String [(String,String)]
  deriving Show

data TTarget = TTarget
  { tName    :: String
  , tCC      :: String
  , tCCFlags :: String
  , tCCLibs  :: String
  , tConf    :: String
  }

findTarget :: String -> [Target] -> Maybe Target
findTarget _ [] = Nothing
findTarget name ((Target n conf):ts) | n == name = Just $ Target n conf
                                     | otherwise = findTarget name ts


-- Parser

type Parser = Prsr [Token] Token

instance TokenMachine [Token] Token where
  tmNextToken [] = (TEnd noSLoc, [])
  tmNextToken (x:xs) = (x,xs)

  tmRawTokens = id


eof :: Parser ()
eof = do
  t <- nextToken
  case t of
    TEnd _ -> pure ()
    _      -> fail "eof"

nl :: Parser [Token]
nl = many $ satisfy "\\n" isWhite
  where isWhite (TIndent _) = True
        isWhite _           = False

spec :: Char -> Parser Token
spec c = satisfy (showToken $ TSpec (SLoc "" 0 0) c) is
  where is (TSpec _ d) = c == d
        is _ = False

ident :: Parser String
ident = satisfyM "key" is
  where is (TIdent _ _ x) = Just x
        is _              = Nothing

key :: Parser String
key = ident

value :: Parser String
value = satisfyM "value" isValue
  where isValue (TString _ x) = Just x
        isValue _             = Nothing

targetName :: Parser String
targetName = spec '[' *> key <* spec ']'

keyValue :: Parser (String, String)
keyValue = (,) <$> key <*> (spec '=' *> value)

keyValues :: Parser [(String,String)]
keyValues = keyValue `sepBy` nl

target :: Parser Target
target = Target <$> (targetName <* nl) <*> keyValues

targets :: Parser [Target]
targets = (target `sepBy1` nl) <* nl <* eof

formatFailed :: LastFail Token -> String
formatFailed (LastFail _ ts msgs) =
  unlines [ showSLoc sloc ++ ":\n"
          , "  found: " ++ head (map showToken ts)
          , "  expected: " ++ unwords (nub msgs)
          ]
  where sloc = tokensLoc ts

parseTargets :: FilePath -> String -> Either String [Target]
parseTargets fp file =
  case runPrsr targets $ lex (SLoc fp 1 1) file of
    Left lf -> Left $ formatFailed lf
    Right a -> Right a
