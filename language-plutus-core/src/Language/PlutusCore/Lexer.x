{
    {-# OPTIONS_GHC -fno-warn-unused-imports #-}
    {-# LANGUAGE OverloadedStrings  #-}
    {-# LANGUAGE StandaloneDeriving #-}
    {-# LANGUAGE DeriveAnyClass        #-}
    {-# LANGUAGE DeriveGeneric         #-}
    {-# LANGUAGE OverloadedStrings     #-}
    {-# LANGUAGE StandaloneDeriving    #-}
    {-# LANGUAGE ScopedTypeVariables   #-}
    {-# LANGUAGE FlexibleContexts      #-}
    {-# LANGUAGE FlexibleInstances     #-}
    {-# LANGUAGE MultiParamTypeClasses #-}
    module Language.PlutusCore.Lexer ( alexMonadScan
                                     , runAlex
                                     , runAlexST
                                     , runAlexST'
                                     -- * Types
                                     , AlexPosn (..)
                                     , Alex (..)
                                     , ParseError (..)
                                     ) where

import PlutusPrelude
import qualified Data.ByteString.Lazy as BSL
import qualified Data.ByteString.Lazy.Char8 as ASCII
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc.Internal (Doc (Text))
import Language.PlutusCore.Lexer.Type
import Language.PlutusCore.PrettyCfg
import Language.PlutusCore.Name
import Control.Monad.Except
import Control.Monad.State

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

@special = \\\\ | \\\"

tokens :-

    <0> $white+                  ;
    <0> "--".*                   ;
    <0> "{-"                     { \_ _ -> nested_comment }

    -- Keywords
    <0> abs                      { mkKeyword KwAbs }
    <0> lam                      { mkKeyword KwLam }
    <0> fix                      { mkKeyword KwFix }
    <0> fun                      { mkKeyword KwFun }
    <0> all                      { mkKeyword KwAll }
    <0> bytestring               { mkKeyword KwByteString }
    <0> integer                  { mkKeyword KwInteger }
    <0> size                     { mkKeyword KwSize }
    <0> type                     { mkKeyword KwType }
    <0> program                  { mkKeyword KwProgram }
    <0> con                      { mkKeyword KwCon }
    <0> wrap                     { mkKeyword KwWrap }
    <0> unwrap                   { mkKeyword KwUnwrap }
    <0> error                    { mkKeyword KwError }

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
    <0> concatenate              { mkBuiltin Concatenate }
    <0> takeByteString           { mkBuiltin TakeByteString }
    <0> dropByteString           { mkBuiltin DropByteString }
    <0> equalsByteString         { mkBuiltin EqByteString }
    <0> resizeByteString         { mkBuiltin ResizeByteString }
    <0> "sha2_256"               { mkBuiltin SHA2 }
    <0> "sha3_256"               { mkBuiltin SHA3 }
    <0> verifySignature          { mkBuiltin VerifySignature }
    <0> equalsByteString         { mkBuiltin EqByteString }
    <0> txhash                   { mkBuiltin TxHash }
    <0> blocknum                 { mkBuiltin BlockNum }
    <0> blocktime                { mkBuiltin BlockTime }

    -- Various special characters
    <0> "("                      { mkSpecial OpenParen }
    <0> ")"                      { mkSpecial CloseParen }
    <0> "["                      { mkSpecial OpenBracket }
    <0> "]"                      { mkSpecial CloseBracket }
    <0> "."                      { mkSpecial Dot }
    <0> "!"                      { mkSpecial Exclamation }
    <0> "{"                      { mkSpecial OpenBrace }
    <0> "}"                      { mkSpecial CloseBrace }

    -- ByteStrings
    <0> \# ($hex_digit{2})*      { tok (\p s -> alex $ LexBS p (asBSLiteral s)) }

    -- Integer/size literals
    <0> @size                    { tok (\p s -> alex $ LexNat p (readBSL s)) }
    <0> @integer                 { tok (\p s -> alex $ LexInt p (readBSL $ stripPlus s)) }

    -- Identifiers
    <0> @identifier              { tok handle_identifier }

{

deriving instance Generic AlexPosn
deriving instance NFData AlexPosn

instance Pretty (AlexPosn) where
    pretty (AlexPn _ line col) = pretty line <> ":" <> pretty col

handleChar :: Word8 -> Word8
handleChar x
    | x >= 48 && x <= 57 = x - 48 -- hexits 0-9
    | x >= 97 && x <= 102 = x - 87 -- hexits a-f
    | x >= 65 && x <= 70 = x - 55 -- hexits A-F
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

mkSpecial = constructor LexSpecial

mkBuiltin = constructor LexBuiltin

mkKeyword = constructor LexKeyword

handle_identifier :: AlexPosn -> BSL.ByteString -> Alex (Token AlexPosn)
handle_identifier p str = do
    s1 <- gets alex_ust
    let (u, s2) = runState (newIdentifier str) s1
    modify (\s -> s { alex_ust = s2})
    pure $ LexName p str u

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

-- | An error encountered during parsing.
data ParseError = LexErr String
                | Unexpected (Token AlexPosn)
                | Overflow AlexPosn Natural Integer 
                deriving (Show, Eq, Generic, NFData)

instance PrettyCfg ParseError where
    prettyCfg _ (LexErr s) = "Lexical error:" <+> Text (length s) (T.pack s)
    prettyCfg cfg (Unexpected t) = "Unexpected" <+> squotes (prettyCfg cfg t) <+> "at" <+> pretty (loc t)
    prettyCfg _ (Overflow pos _ _) = "Integer overflow at" <+> pretty pos <> "."

liftError :: Either String a -> Either ParseError a
liftError(Left s) = Left $ LexErr s
liftError(Right a) = Right $ a

runAlexST :: ByteString.ByteString -> Alex a -> IdentifierState -> Either ParseError (IdentifierState, a)
runAlexST input (Alex f) initial = liftError $ first alex_ust <$>
    f (AlexState { alex_pos = alexStartPos
                 , alex_bpos = 0
                 , alex_inp = input
                 , alex_chr = '\n'
                 , alex_ust = initial
                 , alex_scd = 0
                 })

runAlexST' :: forall a. ByteString.ByteString -> Alex a -> StateT IdentifierState (Except ParseError) a
runAlexST' input al = StateT $ \is -> let
        run :: Either ParseError (a, IdentifierState)
        run = case runAlexST input al is of
            Left e -> Left e
            Right (s, a) -> Right (a, s)
    in liftEither run

}
