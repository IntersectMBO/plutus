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
import Language.PlutusCore.Core

import qualified Data.ByteString.Lazy as BSL
import qualified Data.ByteString.Lazy.Char8 as ASCII
import Language.PlutusCore.Error
import Language.Haskell.TH.Syntax (Lift)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Data.Text.Prettyprint.Doc.Internal (Doc (Text))
import Control.Monad.Except
import Control.Monad.State

{- This version of the lexer relaxes the syntax so that keywords (con,
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
   used for built in names and built in type names. -}

}

%wrapper "monadUserState-bytestring"

$digit = 0-9
$hex_digit = [$digit a-f A-F]
$lower = [a-z]
$upper = [A-Z]

@sign = "+" | "-" | ""

@nat = $digit+
@integer = @sign $digit+
@exp = [eE] @sign $digit+
@float = @sign $digit+ (\. $digit+ (@exp | "") | @exp)

@name = [$lower $upper][$lower $upper $digit \_ \']*

@builtinid  = [$lower $upper][$lower $upper $digit \_ \']*

@special = \\\\ | \\\"


tokens :-

    $white+                  ;
    "--".*                   ;
    "{-"                     { \_ _ -> nested_comment }

    -- Keywords: we only expect these after '('; elsewhere they can be used freely as identifiers 
    <kwd> abs            { mkKeyword KwAbs         `andBegin` 0 } 
    <kwd> lam            { mkKeyword KwLam         `andBegin` 0 }
    <kwd> ifix           { mkKeyword KwIFix        `andBegin` 0 }
    <kwd> fun            { mkKeyword KwFun         `andBegin` 0 }
    <kwd> all            { mkKeyword KwAll         `andBegin` 0 }
    <kwd> type           { mkKeyword KwType        `andBegin` 0 }
    <kwd> program        { mkKeyword KwProgram     `andBegin` 0 }
    <kwd> con            { mkKeyword KwCon         `andBegin` conarg }
    <kwd> iwrap          { mkKeyword KwIWrap       `andBegin` 0 }
    <kwd> unwrap         { mkKeyword KwUnwrap      `andBegin` 0 }
    <kwd> error          { mkKeyword KwError       `andBegin` 0 }
    <kwd> builtin        { mkKeyword KwBuiltin     `andBegin` bin }
    -- ^ Switch the lexer into a mode where it's looking for a builtin id.
    -- These are converted into Builtin names (possibly dynamic) in the parser
    -- Outside this mode, all ids are parsed as Names. 
    
    <conarg> bytestring  { mkKeyword KwByteString  `andBegin` 0 }
    <conarg> integer     { mkKeyword KwInteger     `andBegin` 0 }
    <conarg> string      { mkKeyword KwString      `andBegin` 0 }

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

    -- ByteStrings
    \# ($hex_digit{2})*      { tok (\p s -> alex $ TkBS p (asBSLiteral s)) }

    -- Strings
    <conarg> [\"A-Za-z_]*    { tok (\p s -> alex $ TkString p (show s)) } -- FIXME: proper strings

    -- Integer/size literals
    @nat                     { tok (\p s -> alex $ TkNat p (readBSL s)) }
    @integer                 { tok (\p s -> alex $ TkInt p (readBSL $ stripPlus s)) }

    -- Identifiers
    <0> @name                { tok (\p s -> handle_name p (T.decodeUtf8 (BSL.toStrict s))) }

    <bin> @builtinid         { tok (\p s -> alex $ TkBuiltinId p (T.decodeUtf8 (BSL.toStrict s))) `andBegin` 0 }
{

deriving instance Generic AlexPosn
deriving instance NFData AlexPosn
deriving instance Lift AlexPosn
deriving instance Ord AlexPosn

instance Pretty (AlexPosn) where
    pretty (AlexPn _ line col) = pretty line <> ":" <> pretty col

trimBytes :: BSL.ByteString -> BSL.ByteString
trimBytes str = BSL.take (BSL.length str - 5) str

handleChar :: Word8 -> Word8
handleChar x
    | x >= 48 && x <= 57 = x - 48  -- hexits 0-9
    | x >= 97 && x <= 102 = x - 87 -- hexits a-f
    | x >= 65 && x <= 70 = x - 55  -- hexits A-F
    | otherwise = undefined -- safe b/c macro only matches hexits

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

-- Taken from example by Simon Marlow.
-- This handles Haskell-style comments
nested_comment :: Alex (Token AlexPosn)
nested_comment = go 1 =<< alexGetInput

    where go :: Int -> AlexInput -> Alex (Token AlexPosn)
          go 0 input = alexSetInput input >> alexMonadScan
          go n input =
            case alexGetByte input of
                Nothing -> err input
                Just (c, input') ->
                    case c of
                        45 ->
                            case alexGetByte input' of
                                Nothing -> err input'
                                Just (125,input'') -> go (n-1) input''
                                Just (_,input'') -> go n input''
                        123 ->
                            case alexGetByte input' of
                                Nothing -> err input'
                                Just (c',input'') -> go (addLevel c' $ n) input''
                        _ -> go n input'

          addLevel c' = bool id (+1) (c'==45)

          err (pos,_,_,_) =
            let (AlexPn _ line col) = pos in
                alexError ("Error in nested comment at line " ++ show line ++ ", column " ++ show col)

constructor c t = tok (\p _ -> alex $ c p t)

mkSpecial    = constructor TkSpecial

mkKeyword    = constructor TkKeyword

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
