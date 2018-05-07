{
    module Language.PlutusNapkin.Parser ( parse
                                        ) where

import qualified Data.ByteString.Lazy as BSL
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

    isa { LexKeyword $$ KwIsa }
    abs { LexKeyword $$ KwAbs }
    inst { LexKeyword $$ KwInst }
    lam { LexKeyword $$ KwLam }
    fix { LexKeyword $$ KwFix }
    builtin { LexKeyword $$ KwBuiltin }
    fun { LexKeyword $$ KwFun }
    forall { LexKeyword $$ KwForall }
    size { LexKeyword $$ KwSize }
    integer { LexKeyword $$ KwInteger }
    float { LexKeyword $$ KwFloat }
    bytestring { LexKeyword $$ KwByteString }

    openParen { LexSpecial $$ OpenParen }
    closeParen { LexSpecial $$ CloseParen }
    openBracket { LexSpecial $$ OpenBracket }
    closeBracket { LexSpecial $$ CloseBracket }

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

Term : var { Var (extract $1) (Name (extract $1) (get_identifier $1)) }

{

liftErr :: Either String (Either ParseError a) -> Either ParseError a
liftErr (Left s)  = Left (LexErr s)
liftErr (Right x) = x

parse :: BSL.ByteString -> Either ParseError (Term AlexPosn)
parse str = liftErr (runAlex str (runExceptT parsePlutusNapkin))

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
