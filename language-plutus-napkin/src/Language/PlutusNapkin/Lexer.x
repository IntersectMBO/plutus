{
    {-# OPTIONS_GHC -fno-warn-name-shadowing -fno-warn-unused-imports #-}
    module Language.PlutusNapkin.Lexer ( alexMonadScan
                                       , runAlex
                                       , alexEOF
                                       ) where

import GHC.Natural
import qualified Data.ByteString.Lazy as BSL
import qualified Data.ByteString.Lazy.Char8 as ASCII
import Control.Arrow
import Language.PlutusNapkin.Type
import Language.PlutusNapkin.Identifier

}

%wrapper "monadUserState-bytestring"

$digit = 0-9
$hex_digit = [a-f A-F 0-9]
$lower = [a-z]
$upper = [A-Z]

@sign = "+" | "-" | ""

@integer = @sign $digit+
@exp = [eE] @sign $digit+
@float = @sign $digit+ (\. $digit+ (@exp | "") | @exp)
@size = $digit+

@identifier = $lower [$lower $upper $digit \_ \']*

tokens :-

    <0> $white+                  ;

    -- Keywords
    <0> isa                      { keyword KwIsa }
    <0> abs                      { keyword KwAbs }
    <0> inst                     { keyword KwInst }
    <0> lam                      { keyword KwLam }
    <0> fix                      { keyword KwFix }
    <0> builtin                  { keyword KwBuiltin }
    <0> fun                      { keyword KwFun }
    <0> forall                   { keyword KwForall }
    <0> bytestring               { keyword KwByteString }
    <0> integer                  { keyword KwInteger }
    <0> float                    { keyword KwFloat }
    <0> size                     { keyword KwSize }
    <0> type                     { keyword KwType }

    -- Builtins
    <0> addInteger               { builtin AddInteger }
    <0> subtractInteger          { builtin SubtractInteger }
    <0> multiplyInteger          { builtin MultiplyInteger}
    <0> divideInteger            { builtin DivideInteger }
    <0> remainderInteger         { builtin RemainderInteger }
    <0> lessThanInteger          { builtin LessThanInteger }
    <0> lessThanEqualsInteger    { builtin LessThanEqInteger }
    <0> greaterThanInteger       { builtin GreaterThanInteger }
    <0> greaterThanEqualsInteger { builtin GreaterThanEqInteger }
    <0> equalsInteger            { builtin EqInteger }

    <0> @integer                 { tok (\p s -> alex $ LexInt p (readBSL s)) }
    <0> @float                   { tok (\p s -> alex $ LexFloat p (readBSL s)) }
    <0> @size                    { tok (\p s -> alex $ LexSize p (readBSL s)) }

    <0> @identifier              { tok handle_identifier }

{

constructor c t = tok (\p _ -> alex $ c p t)

builtin = constructor LexBuiltin

keyword = constructor LexKeyword

handle_identifier :: AlexPosn -> BSL.ByteString -> Alex (Token AlexPosn)
handle_identifier p s =
    sets_alex (modifyUST (snd . newIdentifier s)) >> 
    LexName p <$> gets_alex (fst . newIdentifier s . alex_ust)

-- this conversion is safe because we only lex digits
-- FIXME this messes up when we feed it a string like +15
readBSL :: (Read a) => BSL.ByteString -> a
readBSL = read . ASCII.unpack

alex :: a -> Alex a
alex = pure

tok f (p,_,s,_) len = f p (BSL.take len s)

type AlexUserState = IdentifierState

alexInitUserState :: AlexUserState
alexInitUserState = emptyIdentifierState

modifyUST :: (AlexUserState -> AlexUserState) -> AlexState -> AlexState
modifyUST f st = st { alex_ust = f (alex_ust st) }

sets_alex :: (AlexState -> AlexState) -> Alex ()
sets_alex f = Alex (Right . (f &&& pure ()))

gets_alex :: (AlexState -> a) -> Alex a
gets_alex f = Alex (Right . (id &&& f))

get_pos :: Alex AlexPosn
get_pos = gets_alex alex_pos

alexEOF :: Alex (Token AlexPosn)
alexEOF = EOF <$> get_pos

}
