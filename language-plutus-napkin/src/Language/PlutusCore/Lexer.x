{
    {-# OPTIONS_GHC -fno-warn-name-shadowing -fno-warn-unused-imports #-}
    {-# LANGUAGE DeriveAnyClass     #-}
    {-# LANGUAGE DeriveGeneric      #-}
    {-# LANGUAGE StandaloneDeriving #-}
    module Language.PlutusCore.Lexer ( alexMonadScan
                                     , runAlexST
                                     -- * Types
                                     , AlexPosn (..)
                                     , Alex (..)
                                     , AlexState (..)
                                     ) where

import PlutusPrelude
import qualified Data.ByteString.Lazy as BSL
import qualified Data.ByteString.Lazy.Char8 as ASCII
import Language.PlutusCore.Type
import Language.PlutusCore.Identifier

}

%wrapper "monadUserState-bytestring"

$digit = 0-9
$hex_digit = [$digit a-f A-F]
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
    <0> "--".*                   ;
    <0> "{-"                     { \_ _ -> nested_comment }

    -- Keywords
    <0> isa                      { mkKeyword KwIsa }
    <0> abs                      { mkKeyword KwAbs }
    <0> inst                     { mkKeyword KwInst }
    <0> lam                      { mkKeyword KwLam }
    <0> fix                      { mkKeyword KwFix }
    <0> builtin                  { mkKeyword KwBuiltin }
    <0> fun                      { mkKeyword KwFun }
    <0> forall                   { mkKeyword KwForall }
    <0> bytestring               { mkKeyword KwByteString }
    <0> integer                  { mkKeyword KwInteger }
    <0> size                     { mkKeyword KwSize }
    <0> type                     { mkKeyword KwType }
    <0> program                  { mkKeyword KwProgram }

    -- Builtins
    <0> addInteger               { mkBuiltin AddInteger }
    <0> subtractInteger          { mkBuiltin SubtractInteger }
    <0> multiplyInteger          { mkBuiltin MultiplyInteger}
    <0> divideInteger            { mkBuiltin DivideInteger }
    <0> remainderInteger         { mkBuiltin RemainderInteger }
    <0> lessThanInteger          { mkBuiltin LessThanInteger }
    <0> lessThanEqualsInteger    { mkBuiltin LessThanEqInteger }
    <0> greaterThanInteger       { mkBuiltin GreaterThanInteger }
    <0> greaterThanEqualsInteger { mkBuiltin GreaterThanEqInteger }
    <0> equalsInteger            { mkBuiltin EqInteger }
    <0> intToByteString          { mkBuiltin IntToByteString }
    <0> ceil                     { mkBuiltin Ceiling }
    <0> floor                    { mkBuiltin Floor }
    <0> round                    { mkBuiltin Round }
    <0> concatenate              { mkBuiltin Concatenate }
    <0> takeByteString           { mkBuiltin TakeByteString }
    <0> dropByteString           { mkBuiltin DropByteString }
    <0> "sha2_256"               { mkBuiltin SHA2 }
    <0> "sha3_256"               { mkBuiltin SHA3 }
    <0> verifySignature          { mkBuiltin VerifySignature }
    <0> equalsByteString         { mkBuiltin EqByteString }
    <0> txhash                   { mkBuiltin TxHash }
    <0> blocknum                 { mkBuiltin BlockNum }
    <0> blocktime                { mkBuiltin BlockTime }

    <0> "("                      { mkSpecial OpenParen }
    <0> ")"                      { mkSpecial CloseParen }
    <0> "["                      { mkSpecial OpenBracket }
    <0> "]"                      { mkSpecial CloseBracket }
    <0> "."                      { mkSpecial Dot }

    <0> @integer                 { tok (\p s -> alex $ LexInt p (readBSL $ stripPlus s)) }
    <0> @size                    { tok (\p s -> alex $ LexSize p (readBSL s)) }

    -- TODO string literals

    <0> @identifier              { tok handle_identifier }

{

deriving instance Generic AlexPosn
deriving instance NFData AlexPosn

-- Taken from example by Simon Marlow.
-- This provides Haskell-style comments for Plutus Core
nested_comment :: Alex (Token AlexPosn)
nested_comment = go 1 =<< alexGetInput

    where go :: Int -> AlexInput -> Alex (Token AlexPosn)
          go 0 input = alexSetInput input >> alexMonadScan
          go n input =
            case alexGetByte input of
                Nothing -> err input
                Just (c, input') ->
                    case Data.Char.chr (fromIntegral c) of
                        '-' ->
                            case alexGetByte input' of
                                Nothing -> err input'
                                Just (125,input_) -> go (n-1) input_
                                Just (_,input_) -> go n input_
                        '{' ->
                            case alexGetByte input' of
                                Nothing -> err input'
                                Just (c',input'') -> go (addLevel c' $ n) input''
                        _ -> go n input'

          addLevel c' = bool id (+1) (c'==45)

          err (pos,_,_,_) =
            let (AlexPn _ line col) = pos in
                alexError ("Error in nested comment at line " ++ show line ++ ", column " ++ show col)

constructor c t = tok (\p _ -> alex $ c p t)

mkSpecial = constructor LexSpecial

mkBuiltin = constructor LexBuiltin

mkKeyword = constructor LexKeyword

handle_identifier :: AlexPosn -> BSL.ByteString -> Alex (Token AlexPosn)
handle_identifier p s =
    sets_alex (modifyUST (snd . newIdentifier s)) >> 
    LexName p <$> gets_alex (fst . newIdentifier s . alex_ust)

-- this conversion is safe because we only lex digits
-- FIXME this messes up when we feed it a string like +15
readBSL :: (Read a) => BSL.ByteString -> a
readBSL = read . ASCII.unpack

stripPlus :: BSL.ByteString -> BSL.ByteString
stripPlus b = if BSL.head b == 43 then BSL.tail b else b

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

runAlexST :: BSL.ByteString -> Alex a -> Either String (AlexState, a)
runAlexST input (Alex f) = f st
    where st = AlexState { alex_pos = alexStartPos
                         , alex_bpos = 0
                         , alex_inp = input
                         , alex_chr = '\n'
                         , alex_ust = alexInitUserState
                         , alex_scd = 0 
                         }

}
