{
    {-# OPTIONS_GHC -fno-warn-unused-imports #-}
    {-# LANGUAGE OverloadedStrings     #-}
    {-# LANGUAGE DeriveAnyClass        #-}
    {-# LANGUAGE OverloadedStrings     #-}
    {-# LANGUAGE FlexibleInstances     #-}
    {-# LANGUAGE DeriveAnyClass        #-}
    {-# LANGUAGE OverloadedStrings     #-}
    {-# LANGUAGE MultiParamTypeClasses #-}

module Language.PlutusCore.Lexer ( alexMonadScan
                                 , runAlexST'
                                 -- * Types
                                 , AlexPosn (..)
                                 , Alex (..)
                                 ) where

import PlutusPrelude

import Language.PlutusCore.Lexer.Type
import Language.PlutusCore.Name

import qualified Data.ByteString.Lazy as BSL
import qualified Data.ByteString.Lazy.Char8 as ASCII
import Language.PlutusCore.Error
import Language.Haskell.TH.Syntax (Lift)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Data.Text.Prettyprint.Doc.Internal (Doc (Text))
import Control.Monad.Except
import Control.Monad.State
import Text.Read (readMaybe)

{- Note [Keywords]
   This version of the lexer relaxes the syntax so that keywords (con,
   lam, ...) and built in names can be re-used as variable names.  The
   Plutus compiler produces code with such names: for example, the
   builtin `addInteger` is always called via a variable of the same
   name which is bound to a lambda wrapping an invocation of the
   actual builtin.  To achieve this, we use alex's "start codes" which
   allow you to put the lexer into modes in which only certain actions
   are valid.  In the PLC grammar, keywords like `abs`, `con` and so
   on can only occur after a `(`, so when we see one of these we put
   the lexer into a special mode where these are interpreted as
   keywords and converted into elements of the LexKeyword type; having
   done this, we return to the initial lexer state, denoted by 0,
   where we can use keywords as variable names. A similar strategy is
   used for built in type names. -}

}

%wrapper "monadUserState-bytestring"

$digit = 0-9
$hex_digit = [$digit a-f A-F]
$lower = [a-z]
$upper = [A-Z]

@sign = "+" | "-" | ""

@nat = $digit+
--@exp = [eE] @sign $digit+
--@float = @sign $digit+ (\. $digit+ (@exp | "") | @exp)

@name = [$lower $upper][$lower $upper $digit \_ \']*

@builtinid  = [$lower $upper][$lower $upper $digit \_ \']*

@special = \\\\ | \\\"

$graphic = $printable # $white
@quotedstring = \" ($graphic)* \"
@quotedchar   = ' ($graphic)* ' -- Allow multiple characters so we can handle escape sequences
@charseq      = [0-9A-Za-z]+

tokens :-

    $white+                  ;
    "--".*                   ;
    "{-"                     { \_ _ -> nested_comment }

    -- Keywords: we only expect these after '('; elsewhere they can be
    -- used freely as identifiers: see Note [Keywords].
    <kwd> abs            { mkKeyword KwAbs         `andBegin` 0 } 
    <kwd> lam            { mkKeyword KwLam         `andBegin` 0 }
    <kwd> ifix           { mkKeyword KwIFix        `andBegin` 0 }
    <kwd> fun            { mkKeyword KwFun         `andBegin` 0 }
    <kwd> all            { mkKeyword KwAll         `andBegin` 0 }
    <kwd> type           { mkKeyword KwType        `andBegin` 0 }
    <kwd> program        { mkKeyword KwProgram     `andBegin` 0 }
    <kwd> iwrap          { mkKeyword KwIWrap       `andBegin` 0 }
    <kwd> unwrap         { mkKeyword KwUnwrap      `andBegin` 0 }
    <kwd> error          { mkKeyword KwError       `andBegin` 0 }
    <kwd> builtin        { mkKeyword KwBuiltin     `andBegin` bin }
    -- ^ Switch the lexer into a mode where it's looking for a builtin id.
    -- These are converted into Builtin names (possibly dynamic) in the parser
    -- Outside this mode, all ids are parsed as Names. 
    <kwd> con            { mkKeyword KwCon         `andBegin` conargs }
    -- (con type ...): ... can be "()" or or a single or double-quoted string containing spaces,
    -- or any sequence of non-whitespace characters apart from `(` and `)`.  Comment characters
    -- are also allowed, but not treated specially.
    
    <conargs>  @name { tok (\p s -> alex $ TkBuiltinTypeId p (stringOf s)) `andBegin` twaddle }


    -- Maybe we should also do this in the parser, but there's some
    -- ambiguity because literal constants are also parsed here (they
    -- have no start code, so can appear in any context).  There's a
    -- danger that if we save an id here and later parse it into a
    -- builtin type name, it'd actually be a builtin constant.  That
    -- can't happen yet, but could if someone adds `nil` or something.


    -- Various special characters
    "("                  { mkSpecial OpenParen  `andBegin` kwd }
    ")"                  { mkSpecial CloseParen `andBegin` 0}
    "["                  { mkSpecial OpenBracket }
    "]"                  { mkSpecial CloseBracket }
    "."                  { mkSpecial Dot }
    "{"                  { mkSpecial OpenBrace }
    "}"                  { mkSpecial CloseBrace }


    -- Unit
      <twaddle> "()"            { tok (\p s -> alex $ TkLiteral p (stringOf s)) `andBegin` 0 }

    -- Characters
--    <twaddle> @quotedchar     { tok (\p s -> alex $ p s) `andBegin` 0 }

    -- Strings
--    <twaddle> @quotedstring   { tok (\p s -> alex $ p s) `andBegin` 0 }

    -- Others
      <twaddle> @charseq        { tok (\p s -> alex $ TkLiteral p (stringOf s)) `andBegin` 0 }

    -- Natural literal, used in version numbers
    <0> @nat                     { tok (\p s -> alex $ TkNat p (readBSL s)) }
    
    -- Identifiers
    <0> @name                { tok (\p s -> handle_name p (textOf s)) }

    <bin> @builtinid         { tok (\p s -> alex $ TkBuiltinId p (textOf s)) `andBegin` 0 }

{

deriving instance Generic AlexPosn
deriving instance NFData AlexPosn
deriving instance Lift AlexPosn
deriving instance Ord AlexPosn

instance Pretty (AlexPosn) where
    pretty (AlexPn _ line col) = pretty line <> ":" <> pretty col

trimBytes :: BSL.ByteString -> BSL.ByteString
trimBytes str = BSL.take (BSL.length str - 5) str

ord8 :: Char -> Word8
ord8 = fromIntegral . Data.Char.ord

chr8 :: Word8 -> Char
chr8 = Data.Char.chr . fromIntegral

handleChar :: Word8 -> Word8
handleChar x =
    let c :: Char = Data.Char.chr (fromIntegral x)
    in    if c >= '0' && c <= '9'  then x - ord8 '0'
    else  if c >= 'a' && c <= 'f'  then x - ord8 'a' + 10
    else  if c >= 'A' && c <= 'F'  then x - ord8 'A' + 10
    else  undefined -- safe b/c macro only matches hex digits


textOf = T.decodeUtf8 . BSL.toStrict

stringOf = T.unpack . T.decodeUtf8 . BSL.toStrict

-- turns a pair of bytes such as "a6" into a single Word8
handlePair :: Word8 -> Word8 -> Word8
handlePair c c' = 16 * handleChar c + handleChar c'

asBytes :: [Word8] -> [Word8]
asBytes [] = mempty
asBytes (c:c':cs) = handlePair c c' : asBytes cs
asBytes _ = undefined -- safe b/c macro matches them in pairs

asBSLiteral :: BSL.ByteString -> BSL.ByteString
asBSLiteral = withBytes asBytes . BSL.tail
    where withBytes f = BSL.pack . f . BSL.unpack

-- Convert a single-quoted string to a character.  This should handle escape codes correctly.
getCharLiteral :: BSL.ByteString -> Char
getCharLiteral s =
    let str = ASCII.unpack s
    in case Text.Read.readMaybe str :: Maybe Char of
       Just c -> c
       Nothing -> error $ "Lexical error: invalid character constant " ++ str
       -- Using error here isn't ideal, but it'll go away when types can supply their own parsers

-- Taken from example by Simon Marlow.
-- This handles Haskell-style comments
nested_comment :: Alex (Token AlexPosn)
nested_comment = go 1 =<< alexGetInput

    where go :: Int -> AlexInput -> Alex (Token AlexPosn)
          go 0 input = alexSetInput input >> alexMonadScan
          go n input =
            case alexGetChar input of
                Nothing -> err input
                Just (c, input') ->
                    case c of
                        '-' ->
                            case alexGetChar input' of
                                Nothing -> err input'
                                Just ('}', input'') -> go (n-1) input''
                                Just (_,input'') -> go n input''
                        '{' ->
                            case alexGetChar input' of
                                Nothing -> err input'
                                Just (c',input'') -> go (addLevel c' $ n) input''
                        _ -> go n input'

          addLevel c' = bool id (+1) (c' == '-')

          alexGetChar = fmap (first chr8) . alexGetByte

          err (pos,_,_,_) =
            let (AlexPn _ line col) = pos in
                alexError ("Error in nested comment at line " ++ show line ++ ", column " ++ show col)

constructor c t = tok (\p _ -> alex $ c p t)

mkSpecial = constructor TkSpecial

mkKeyword = constructor TkKeyword

handle_name :: AlexPosn -> T.Text -> Alex (Token AlexPosn)
handle_name p str = do
    s1 <- gets alex_ust
    let (u, s2) = runState (newIdentifier str) s1
    modify (\s -> s { alex_ust = s2})
    pure $ TkName p str u

-- this conversion is safe because we only lex digits
readBSL :: (Read a) => BSL.ByteString -> a
readBSL = read . ASCII.unpack

-- This strips off the initial '+' from a bytestring so that we can use 'read'
-- to get an integer
stripPlus :: BSL.ByteString -> BSL.ByteString
stripPlus b = if BSL.head b == 43 then BSL.tail b else b

alex :: a -> Alex a
alex = pure

tok f (p,_,s,_) len = f p (BSL.take len s)

type AlexUserState = IdentifierState

alexInitUserState :: AlexUserState
alexInitUserState = emptyIdentifierState

instance MonadState AlexState Alex where
    get = Alex (\s -> Right (s, s))
    put s = Alex (\_ -> Right (s, ()))

alexEOF :: Alex (Token AlexPosn)
alexEOF = EOF . alex_pos <$> get

liftError :: Either String a -> Either (ParseError b) a
liftError(Left s)  = Left $ LexErr s
liftError(Right a) = Right $ a

runAlexST :: ByteString.ByteString -> Alex a -> IdentifierState -> Either (ParseError AlexPosn) (IdentifierState, a)
runAlexST input (Alex f) initial = liftError $ first alex_ust <$>
    f (AlexState { alex_pos = alexStartPos
                 , alex_bpos = 0
                 , alex_inp = input
                 , alex_chr = '\n'
                 , alex_ust = initial
                 , alex_scd = 0
                 })

runAlexST' :: forall a. ByteString.ByteString -> Alex a -> StateT IdentifierState (Except (ParseError AlexPosn)) a
runAlexST' input al = StateT $ \is -> let
        run :: Either (ParseError AlexPosn) (a, IdentifierState)
        run = case runAlexST input al is of
            Left e -> Left e
            Right (s, a) -> Right (a, s)
    in liftEither run

}
