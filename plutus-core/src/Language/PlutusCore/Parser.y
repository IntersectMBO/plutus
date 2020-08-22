{
    {-# LANGUAGE OverloadedStrings  #-}
    {-# LANGUAGE TypeApplications   #-}
    {-# LANGUAGE TypeOperators      #-}
    {-# LANGUAGE LambdaCase         #-}
module Language.PlutusCore.Parser ( parse
				  , parseTm
				  , parseTy
				  , parseST
				  , parseTermST
				  , parseTypeST
				  , parseProgram
                                  , parseTerm
				  , parseType
				  , ParseError (..)
				  ) where
   
import PlutusPrelude

import Language.PlutusCore.Core.Type
import Language.PlutusCore.Error
import Language.PlutusCore.Lexer.Type
import Language.PlutusCore.Lexer
import Language.PlutusCore.Quote
import Language.PlutusCore.Constant.Dynamic
import Language.PlutusCore.Constant.Typed
import Language.PlutusCore.Core
import Language.PlutusCore.Name
import Language.PlutusCore.Universe
import Language.PlutusCore.Mark
import Language.PlutusCore.MkPlc          (mkTyBuiltin, mkConstant)

import           Data.ByteString.Lazy     (ByteString)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map
import qualified Data.Text as T
import Text.Read                          (readMaybe)
import Data.Text.Prettyprint.Doc.Internal (Doc (Text))
import Control.Monad.Except
import Control.Monad.State

}

%name parsePlutusCoreProgram Program
%name parsePlutusCoreTerm Term
%name parsePlutusCoreType Type
%tokentype { Token AlexPosn }
%error { parseError }
%monad { Parse } { (>>=) } { pure }
%lexer { lift alexMonadScan >>= } { EOF _ }
%nonassoc integer
%nonassoc float
%nonassoc bytestring
%nonassoc string
%nonassoc iwrap
%nonassoc unwrap
%nonassoc lam
%nonassoc con
%nonassoc bi

%token

    abs           { TkKeyword $$ KwAbs }
    lam           { TkKeyword $$ KwLam }
    ifix          { TkKeyword $$ KwIFix }
    con           { TkKeyword $$ KwCon }
    builtin       { TkKeyword $$ KwBuiltin }
    fun           { TkKeyword $$ KwFun }
    all           { TkKeyword $$ KwAll }
    type          { TkKeyword $$ KwType }
    program       { TkKeyword $$ KwProgram }
    iwrap         { TkKeyword $$ KwIWrap }
    unwrap        { TkKeyword $$ KwUnwrap }
    errorTerm     { TkKeyword $$ KwError }

    openParen     { TkSpecial $$ OpenParen }
    closeParen    { TkSpecial $$ CloseParen }
    openBracket   { TkSpecial $$ OpenBracket }
    closeBracket  { TkSpecial $$ CloseBracket }
    dot           { TkSpecial $$ Dot }
    openBrace     { TkSpecial $$ OpenBrace }
    closeBrace    { TkSpecial $$ CloseBrace }

    naturalLit    { $$@TkNat{} }
    literal       { $$@TkLiteral{} }
    builtintypeid { $$@TkBuiltinTypeId{} }
    name          { $$@TkName{} }
    builtinid     { $$@TkBuiltinId{} }

%%

many(p)
    : many(p) p { $2 : $1 }
    | { [] }

some(p)
    : some(p) p { $2 :| toList $1 }
    | p { $1 :| [] }

parens(p)
    : openParen p closeParen { $2 }

Program : openParen program Version Term closeParen { Program $2 $3 $4 }

Version : naturalLit dot naturalLit dot naturalLit { Version (tkLoc $1) (tkNat $1) (tkNat $3) (tkNat $5) }

Name   : name { Name (tkName $1) (tkIdentifier $1) }

Var    : name { Var (tkLoc $1) (Name (tkName $1) (tkIdentifier $1)) }

TyName : name { TyName (Name (tkName $1) (tkIdentifier $1)) }

TyVar  : name { TyVar (tkLoc $1) (TyName (Name (tkName $1) (tkIdentifier $1))) }

Term : Var                                            { $1 }
     | openParen abs TyName Kind Term closeParen      { TyAbs $2 $3 $4 $5 }
     | openBrace Term some(Type) closeBrace           { tyInst $1 $2 (NE.reverse $3) }
     | openParen lam Name Type Term closeParen        { LamAbs $2 $3 $4 $5 }
     | openBracket Term some(Term) closeBracket       { app $1 $2 (NE.reverse $3) }
     | openParen con builtintypeid literal closeParen { mkBuiltinConstant $2 (tkBuiltinTypeId $3) (tkLiteral $4)}
     | openParen iwrap Type Type Term closeParen      { IWrap $2 $3 $4 $5 }
     | openParen builtin builtinid closeParen         { mkBuiltin $2 (tkBuiltinId $3) }
     | openParen unwrap Term closeParen               { Unwrap $2 $3 }
     | openParen errorTerm Type closeParen            { Error $2 $3 }

Type : TyVar { $1 }
     | openParen fun Type Type closeParen        { TyFun $2 $3 $4 }
     | openParen all TyName Kind Type closeParen { TyForall $2 $3 $4 $5 }
     | openParen lam TyName Kind Type closeParen { TyLam $2 $3 $4 $5 }
     | openParen ifix Type Type closeParen       { TyIFix $2 $3 $4 }
     | openBracket Type some(Type) closeBracket  { tyApps $1 $2 (NE.reverse $3) }
     | openParen con builtintypeid closeParen    { mkBuiltinType $2 (tkBuiltinTypeId $3) }

Kind : parens(type) { Type $1 }
     | openParen fun Kind Kind closeParen { KindArrow $2 $3 $4 }

{
getStaticBuiltinName :: T.Text -> Maybe StaticBuiltinName
getStaticBuiltinName = \case
    "addInteger"               -> Just AddInteger
    "subtractInteger"          -> Just SubtractInteger
    "multiplyInteger"          -> Just MultiplyInteger
    "divideInteger"            -> Just DivideInteger
    "quotientInteger"          -> Just QuotientInteger
    "modInteger"               -> Just ModInteger
    "remainderInteger"         -> Just RemainderInteger
    "lessThanInteger"          -> Just LessThanInteger
    "lessThanEqualsInteger"    -> Just LessThanEqInteger
    "greaterThanInteger"       -> Just GreaterThanInteger
    "greaterThanEqualsInteger" -> Just GreaterThanEqInteger
    "equalsInteger"            -> Just EqInteger
    "concatenate"              -> Just Concatenate
    "takeByteString"           -> Just TakeByteString
    "dropByteString"           -> Just DropByteString
    "equalsByteString"         -> Just EqByteString
    "lessThanByteString"       -> Just LtByteString
    "greaterThanByteString"    -> Just GtByteString
    "sha2_256"                 -> Just SHA2
    "sha3_256"                 -> Just SHA3
    "verifySignature"          -> Just VerifySignature
    "ifThenElse"               -> Just IfThenElse
    _                          -> Nothing


mkBuiltinType :: (DefaultUni <: uni) => a -> String -> Type TyName uni a
mkBuiltinType loc tyname = case tyname of
  "bool"       -> mkTyBuiltin @Bool       loc
  "bytestring" -> mkTyBuiltin @ByteString loc
  "char"       -> mkTyBuiltin @Char       loc
  "integer"    -> mkTyBuiltin @Integer    loc
  "string"     -> mkTyBuiltin @String     loc
  "unit"       -> mkTyBuiltin @()         loc
  _ -> error $ "Unknown type: " ++ tyname

mkBuiltinConstant :: (DefaultUni <: uni) => a -> String -> String -> Term TyName name uni a
mkBuiltinConstant loc tyname lit  =
  case tyname of
  "bool"       -> case lit of
                      "true"  -> mkConstant loc True
                      "false" -> mkConstant loc False
                      _ -> error $ "Invalid literal " ++ show lit ++ " of type " ++ show tyname
  "bytestring" -> undefined  -- eg #123abc, even number of characters.
  "char"       -> undefined
  "integer"    -> case readMaybe lit of 
                     Just (n :: Integer) -> mkConstant loc n
                     Nothing -> error $ "Invalid literal " ++ lit ++ " of type " ++ tyname
  "string"     -> undefined
  "unit"       -> case readMaybe lit of 
                     Just (u :: ()) -> mkConstant loc u
                     Nothing -> error $ "Invalid literal " ++ lit ++ " of type " ++ tyname
  _ -> error $ "Unknown type: " ++ tyname

mkBuiltin :: a -> T.Text -> Term TyName Name uni a
mkBuiltin loc ident = 
   case getStaticBuiltinName ident of 
      Just b  -> Builtin loc $ StaticBuiltinName b
      Nothing -> Builtin loc (DynBuiltinName (DynamicBuiltinName ident))

-- FIXME: at this point it would be good to have access to the current
-- dynamic builtin names to check if a builtin with that name exists
-- and issue an error if not.  Unfortunately that involves adding a
-- parameter of type DynamicBuiltinNameMeanings to almost every
-- function in PlutusPrelude.hs, and others elsewhere.  @effectfully
-- says that his future plans may help with this.  In the meantime,
-- you get a scope resolution error during typechecking/execution if
-- it encounters a nonexistent name.  [We could also have a hard-coded
-- list of known dynamic names here, but that might not be ideal.]

tyInst :: a -> Term tyname name uni a -> NonEmpty (Type tyname uni a) -> Term tyname name uni a
tyInst loc t (ty :| []) = TyInst loc t ty
tyInst loc t (ty :| tys) = TyInst loc (tyInst loc t (ty:|init tys)) (last tys)

tyApps :: a -> Type tyname uni a -> NonEmpty (Type tyname uni a) -> Type tyname uni a
tyApps loc ty (ty' :| [])  = TyApp loc ty ty'
tyApps loc ty (ty' :| tys) = TyApp loc (tyApps loc ty (ty':|init tys)) (last tys)

app :: a -> Term tyname name uni a -> NonEmpty (Term tyname name uni a) -> Term tyname name uni a
app loc t (t' :| []) = Apply loc t t'
app loc t (t' :| ts) = Apply loc (app loc t (t':|init ts)) (last ts)

parseST :: ByteString -> StateT IdentifierState (Except (ParseError AlexPosn)) (Program TyName Name DefaultUni AlexPosn)
parseST str =  runAlexST' str (runExceptT parsePlutusCoreProgram) >>= liftEither

parseTermST :: ByteString -> StateT IdentifierState (Except (ParseError AlexPosn)) (Term TyName Name DefaultUni AlexPosn)
parseTermST str = runAlexST' str (runExceptT parsePlutusCoreTerm) >>= liftEither

parseTypeST :: ByteString -> StateT IdentifierState (Except (ParseError AlexPosn)) (Type TyName DefaultUni AlexPosn)
parseTypeST str = runAlexST' str (runExceptT parsePlutusCoreType) >>= liftEither

mapParseRun :: (AsParseError e a, MonadError e m, MonadQuote m) => StateT IdentifierState (Except (ParseError a)) b -> m b
-- we need to run the parser starting from our current next unique, then throw away the rest of the
-- parser state and get back the new next unique
mapParseRun run = do
    nextU <- liftQuote freshUnique
    (p, (_, u)) <- throwingEither _ParseError $ runExcept $ runStateT run (identifierStateFrom nextU)
    liftQuote $ markNonFreshBelow u
    pure p

-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m) => ByteString -> m (Program TyName Name DefaultUni AlexPosn)
parseProgram str = mapParseRun (parseST str)

-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m) => ByteString -> m (Term TyName Name DefaultUni AlexPosn)
parseTerm str = mapParseRun (parseTermST str)

-- | Parse a PLC type. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseType :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m) => ByteString -> m (Type TyName DefaultUni AlexPosn)
parseType str = mapParseRun (parseTypeST str)

-- | Parse a 'ByteString' containing a Plutus Core program, returning a 'ParseError' if syntactically invalid.
--
parse :: ByteString -> Either (ParseError AlexPosn) (Program TyName Name DefaultUni AlexPosn)
parse str = fmap fst $ runExcept $ runStateT (parseST str) emptyIdentifierState

parseTm :: ByteString -> Either (ParseError AlexPosn) (Term TyName Name DefaultUni AlexPosn)
parseTm str = fmap fst $ runExcept $ runStateT (parseTermST str) emptyIdentifierState

parseTy :: ByteString -> Either (ParseError AlexPosn) (Type TyName DefaultUni AlexPosn)
parseTy str = fmap fst $ runExcept $ runStateT (parseTypeST str) emptyIdentifierState

type Parse = ExceptT (ParseError AlexPosn) Alex

parseError :: Token AlexPosn -> Parse b
parseError = throwError . Unexpected

}
