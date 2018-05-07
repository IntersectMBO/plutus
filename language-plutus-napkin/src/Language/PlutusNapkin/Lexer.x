{
    {-# OPTIONS_GHC -fno-warn-name-shadowing -fno-warn-unused-imports #-}
    module Language.PlutusNapkin.Lexer ( alexMonadScan
                                       , runAlex
                                       , alexEOF
                                       ) where

import qualified Data.ByteString.Lazy as BSL
import Control.Arrow
import Language.PlutusNapkin.Type
import Language.PlutusNapkin.Identifier

}

%wrapper "monadUserState-bytestring"

$digit = 0-9


tokens :-

    <0> $white+                  ;
    <0> addInteger               { tok (\p _ -> alex $ LexBuiltin p AddInteger) }

{

alex :: a -> Alex a
alex = pure

tok f (p,_,s,_) len = f p (BSL.take len s)

type AlexUserState = IdentifierState

alexInitUserState :: AlexUserState
alexInitUserState = emptyIdentifierState

gets_alex :: (AlexState -> a) -> Alex a
gets_alex f = Alex (Right . (id &&& f))

get_pos :: Alex AlexPosn
get_pos = gets_alex alex_pos

alexEOF :: Alex (Name AlexPosn)
alexEOF = EOF <$> get_pos

}
