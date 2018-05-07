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

    -- Builtins
    <0> addInteger               { tok (\p _ -> alex $ LexBuiltin p AddInteger) }
    <0> subtractInteger          { tok (\p _ -> alex $ LexBuiltin p SubtractInteger) }
    <0> multiplyInteger          { tok (\p _ -> alex $ LexBuiltin p MultiplyInteger) }
    <0> divideInteger            { tok (\p _ -> alex $ LexBuiltin p DivideInteger) }
    <0> remainderIntger          { tok (\p _ -> alex $ LexBuiltin p RemainderInteger) }

    <0> @integer                 { tok (\p s -> alex $ LexInt p (readBSL s)) }
    <0> @float                   { tok (\p s -> alex $ LexFloat p (readBSL s)) }
    <0> @size                    { tok (\p s -> alex $ LexSize p (readBSL s)) }

    <0> @identifier              { tok handle_identifier }

{

handle_identifier :: AlexPosn -> BSL.ByteString -> Alex (Token AlexPosn)
handle_identifier p s =
    sets_alex (modifyUST (snd . newIdentifier s)) >> 
    LexVar p <$> gets_alex (fst . newIdentifier s . alex_ust) 

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
