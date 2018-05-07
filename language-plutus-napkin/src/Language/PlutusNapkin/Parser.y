{
    module Language.PlutusNapkin.Parser ( parse
                                        ) where

import Control.Arrow
import qualified Data.ByteString.Lazy as BSL
import Control.Monad.Except
import Control.Monad.Trans.Except
import Language.PlutusNapkin.Lexer
import Language.PlutusNapkin.Identifier
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

Term : var { Var (loc $1) (Name (loc $1) (identifier $1)) }
     | openParen isa Type Term closeParen { TyAnnot $2 $3 $4 }

Type : var { TyVar (loc $1) (Name (loc $1) (identifier $1)) }
     | openParen fun Type Type closeParen { TyFun $2 $3 $4 }

{

parse :: BSL.ByteString -> Either ParseError (IdentifierState, (Term AlexPosn))
parse str = liftErr (go . first alex_ust <$> runAlexST str (runExceptT parsePlutusNapkin))
    where go (st, Left err) = Left err
          go (st, Right x) = Right (st, x)
          liftErr (Left s)  = Left (LexErr s)
          liftErr (Right x) = x

data ParseError = LexErr String
                | Unexpected (Token AlexPosn)
                | Expected AlexPosn [String] String

type Parse = ExceptT ParseError Alex

parseError :: Token AlexPosn -> Parse b
parseError = throwE . Unexpected

}
