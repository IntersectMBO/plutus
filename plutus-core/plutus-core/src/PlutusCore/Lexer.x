{
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module PlutusCore.Lexer ( alexMonadScan
                                 , runAlexST'
                                 -- * Types
                                 , AlexPosn (..)
                                 , Alex (..)
                                 , topAlexPosn
                                 ) where

import PlutusPrelude

import PlutusCore.Error
import PlutusCore.Lexer.Type
import PlutusCore.Name

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

The final item above even allows the possiblity of parsing complex types such as
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

-- Regular expressions for literal constants

-- A single quoted string, allowing escaped characters including \'.
-- This says "Single quotes enclosing a sequence of either (a) printable
-- characters excluding ' and \ , or (b) a blackslash followed by
-- any printable character (single quote included)"
@sqs   = '  ( ($printable # ['\\])  | (\\$printable) )* '

-- A double quoted string, allowing escaped characters including \".  Similar to @sqs
@dqs   = \" ( ($printable # [\"\\]) | (\\$printable) )* \"

-- A sequence of printable characters not containing '(' or ')' such that the
-- first character is not a space or a single or double quote.  If there are any
-- further characters then they must comprise a sequence of printable characters
-- possibly including spaces, followed by a non-space character.  If there are
-- any leading or trailing spaces they will be consumed by the $white+ token
-- below.
$nonparen = $printable # [\(\)]
@chars = ($nonparen # ['\"$white]) ($nonparen* ($nonparen # $white))?

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
    <kwd> force          { mkKeyword KwForce       `andBegin` 0 }
    <kwd> delay          { mkKeyword KwDelay       `andBegin` 0 }
    <kwd> builtin        { mkKeyword KwBuiltin     `andBegin` builtin }
    -- ^ Switch the lexer into a mode where it's looking for a builtin id.
    -- These are converted into Builtin names in the parser.
    -- Outside this mode, all ids are parsed as Names.
    <kwd> con            { mkKeyword KwCon         `andBegin` conargs }
    -- ^ (con tyname) or (con tyname const)

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

    -- Names of built-in functions
    <builtin> @builtinid          { tok (\p s -> alex $ TkBuiltinFnId p (textOf s)) `andBegin` 0 }

    -- Things that can follow 'con': the name of a  built-in type and possibly a literal constant of that type
    <conargs>  @name              { tok (\p s -> alex $ TkBuiltinTypeId p (textOf s)) `andBegin` literalconst }

    -- Literal built-in constants. See Note [Literal Constants].
    <literalconst> "()" | @sqs | @dqs | @chars { tok (\p s -> alex $ TkLiteralConst p (textOf s)) `andBegin` 0 }

{

deriving instance Generic AlexPosn
deriving instance NFData AlexPosn
deriving instance Lift AlexPosn
deriving instance Ord AlexPosn

topAlexPosn :: AlexPosn
topAlexPosn = AlexPn 0 0 0

instance Pretty (AlexPosn) where
    pretty (AlexPn _ line col) = "line " <> pretty line <> ", column " <> pretty col

chr8 :: Word8 -> Char
chr8 = Data.Char.chr . fromIntegral

textOf :: BSL.ByteString -> T.Text
textOf = T.decodeUtf8 . BSL.toStrict

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
