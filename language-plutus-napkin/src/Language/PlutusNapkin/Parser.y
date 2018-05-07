{
    module Language.PlutusNapkin.Parser ( parsePlutusNapkin
                                        ) where

import Control.Monad.Trans.Except
import Control.Monad.Except
import Language.PlutusNapkin.Lexer
import Language.PlutusNapkin.Type

}

%name parsePlutusNapkin
%tokentype { Token AlexPosn }
%error { parseError }
%monad { Parse } { (>>=) } { return }
%lexer { lift alexMonadScan >>= } { EOF _ }
%nonassoc integer
%nonassoc float
%nonassoc bytestring

%token

    integer { LexKeyword $$ KwInteger }
    float { LexKeyword $$ KwFloat }
    bytestring { LexKeyword $$ KwByteString }

    openParen { LexSpecial $$ OpenParen }
    closeParen { LexSpecial $$ CloseParen }

    var { $$@LexName{} }

%%

many(p)
    : many(p) p { $2 : $1 }
    | { [] }

some(p)
    : some(p) p { $2 : $1 }
    | p { [$1] }

parens(p)
    : openParen p closeParen { $2 }

Term : var { Var (extract $1) (get_identifier $1) }

{

data ParseError = LexErr String
                | Unexpected (Token AlexPosn)
                | Expected AlexPosn [String] String

type Parse = ExceptT ParseError Alex

parseError :: Token AlexPosn -> Parse b
parseError = throwE . Unexpected

extract :: Token a -> a
extract (LexName p _) = p
extract (LexInt p _)  = p
extract _ = error "FIXME get rid of this"

get_identifier :: Token a -> Int
get_identifier (LexName _ i) = i
get_identifier _             = error "internal error."

}
