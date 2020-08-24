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

import Language.PlutusCore.Error
import Language.PlutusCore.Lexer.Type
import Language.PlutusCore.Name

import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import           Data.Char (isSpace)
import           Data.Text.Prettyprint.Doc.Internal (Doc (Text))
import qualified Data.ByteString.Lazy       as BSL
import qualified Data.ByteString.Lazy.Char8 as ASCII
import           Language.Haskell.TH.Syntax (Lift)
import           Text.Read (readMaybe)

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

{- Note [Literal Constants]
   For literal constants, we accept certain types of character sequences that are
   then passed to user-defined parsers which convert them to built-in constants.
   Literal constants have to specify the type of the constant, so we have (con
   integer 9), (con string "Hello"), and so on.  This allows us to use the same
   literal syntax for different types (eg, integer, short, etc) and shift most
   of the responsibility for parsing constants out of the lexer and into the
   parser (and eventually out of the parser to parsers supplied by the types
   themselves).

   We allow:
    * ()
    * Single-quoted printable characters
    * Double-quoted sequences of printable characters
    * Unquoted sequences of printable characters not including '(' and ')'

  "Printable" here uses Alex's definition: Unicode code points 32 to 0x10ffff.
  This includes spaces but excludes tabs amongst other things.  One can
  use the usual escape sequences though, as long as the type-specific parser
  deals with them.

  These allow us to parse all of the standard types.  We just return
  all of the characters in a TkLiteral token, not attempting to do things
  like stripping off quotes or interpreting escape sequences: it's the
  responsibility of the parser for the relevant type to do these things.
  Note that 'read' will often do the right thing.

  The final item above even allows the possiblity of parsing complex types such
  as tuples and lists as long as parentheses are not involved.  For example,
  (con tuple <1, 2.3, "yes">) and (con intlist [1, 2, -7]) are accepted by the
  lexer, as is (con intseq 12 4 55 -4).  The final example looks strange, but
  the (imaginary) "intseq" parser would receive the string "12 4 55 -4" as a
  single token.  We can't allow (con )) or (con tuple (1,2,3)) because it
  would be difficult for the lexer to decide when it had reached the end
  of the literal (consider a tuple containing a quoted string containing ')',
  for example).

-}
}

%wrapper "monadUserState-bytestring"

-- $ = character set macro
-- @ = regular expression macro

$digit = 0-9
$lower = [a-z]
$upper = [A-Z]

@nat = $digit+

@name = [$lower $upper][$lower $upper $digit \_ \']*

@builtinid  = [$lower $upper][$lower $upper $digit \_ \']*

@special = \\\\ | \\\"

@quotedstring = \" ($printable)* \"
@quotedchar   = ' ($printable)* ' -- Allow multiple characters so we can handle escape sequences
@charseq      =  ( $printable # [ \( \) ] )+
-- @charseq = ~[ ' \" ] ( $printable # [ \( \) ] )+
-- ^ Don't match single or double quotes or whitespace at the start.
-- This doesn't work.  I wonder why?
-- Without $white, preceding whitespace is included
-- ... except that now we're trimming leading whitespace in stringOf

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
    
    <conargs>  @name { tok (\p s -> alex $ TkBuiltinTypeId p (stringOf s)) `andBegin` literalconst }


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


    -- Natural literal, used in version numbers
    <0> @nat                      { tok (\p s -> alex $ TkNat p (readBSL s)) }
    
    -- Identifiers
    <0> @name                     { tok (\p s -> handle_name p (textOf s)) }

    -- Literal built-in constants
    <literalconst> "()"               { tok (\p s -> alex $ TkLiteral p (stringOf s)) `andBegin` 0 }
    <literalconst>  @quotedchar       { tok (\p s -> alex $ TkLiteral p (stringOf s)) `andBegin` 0 }
    <literalconst>  @quotedstring     { tok (\p s -> alex $ TkLiteral p (stringOf s)) `andBegin` 0 }
    <literalconst>  @charseq          { tok (\p s -> alex $ TkLiteral p (stringOf s)) `andBegin` 0 }
--    <0>  ")"               { mkSpecial CloseParen `andBegin` 0 }
    
    <bin> @builtinid                  { tok (\p s -> alex $ TkBuiltinId p (textOf s)) `andBegin` 0 }

{

deriving instance Generic AlexPosn
deriving instance NFData AlexPosn
deriving instance Lift AlexPosn
deriving instance Ord AlexPosn

instance Pretty (AlexPosn) where
    pretty (AlexPn _ line col) = "line " <> pretty line <> ", column " <> pretty col

chr8 :: Word8 -> Char
chr8 = Data.Char.chr . fromIntegral

textOf :: BSL.ByteString -> T.Text
textOf = T.decodeUtf8 . BSL.toStrict

stringOf :: BSL.ByteString -> String
--stringOf = T.unpack . T.decodeUtf8 . BSL.toStrict
stringOf = dropWhile isSpace . T.unpack . T.decodeUtf8 . BSL.toStrict
-- FIXME: do this with the tokens
   

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

{- Rule (stuff in {}):

{ ... } :: user       -- predicate state
        -> AlexInput  -- input stream before the token
        -> Int        -- length of the token
        -> AlexInput  -- input stream after the token
        -> Bool       -- True <=> accept the token

-}

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
