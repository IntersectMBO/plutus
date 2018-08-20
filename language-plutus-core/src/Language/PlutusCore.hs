{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module Language.PlutusCore
    ( Configuration (..)
    , defaultCfg
    , debugCfg
      -- * Parser
    , parse
    , parseST
    , parseTermST
    , parseTypeST
    , parseScoped
    -- * Pretty-printing
    , prettyText
    , debugText
    , prettyString
    -- * AST
    , Term (..)
    , Type (..)
    , Constant (..)
    , Kind (..)
    , ParseError (..)
    , Version (..)
    , Program (..)
    , Name (..)
    , TyName (..)
    , Unique (..)
    , Size
    , Value
    , BuiltinName (..)
    , TypeBuiltin (..)
    -- * Lexer
    , AlexPosn (..)
    -- * Views
    , IterApp (..)
    , TermIterApp
    , PrimIterApp
    -- * Formatting
    , format
    , formatDoc
    -- * Processing
    , annotate
    , annotateST
    , freshName
    , freshTyName
    , RenameError (..)
    , TyNameWithKind (..)
    , NameWithType (..)
    , Debug (..)
    , TypeState (..)
    , RenamedType
    , RenamedTerm
    , discardAnnsTy
    , discardAnnsTerm
    -- * Normalization
    , check
    , NormalizationError
    -- * Type synthesis
    , typeOf
    , kindOf
    , runTypeCheckM
    , programType
    , fileType
    , printType
    , TypeError (..)
    , TypeCheckM
    , BuiltinTable (..)
    -- * Errors
    , Error (..)
    , IsError (..)
    -- * Base functors
    , TermF (..)
    , TypeF (..)
    ) where

import qualified Data.ByteString.Lazy              as BSL
import qualified Data.IntMap                       as IM
import qualified Data.Text                         as T
import           Data.Text.Prettyprint.Doc         hiding (annotate)
import           Language.PlutusCore.Error
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeSynthesis
import           Language.PlutusCore.View
import           PlutusPrelude
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Functor.Foldable


newtype Configuration = Configuration Bool

-- | Given a file at @fibonacci.plc@, @fileType "fibonacci.plc"@ will display
-- its type or an error message.
fileType :: FilePath -> IO T.Text
fileType = fmap (either prettyText id . printType) . BSL.readFile

-- | Print the type of a program contained in a 'ByteString'
printType :: BSL.ByteString -> Either Error T.Text
printType = collectErrors . fmap (fmap typeText . annotateST) . parseScoped

typeText :: Pretty a => (TypeState a, Program TyNameWithKind NameWithType a) -> T.Text
typeText = uncurry (either prettyText prettyText .* programType 10000)

-- | This is the default 'Configuration' most users will want
defaultCfg :: Configuration
defaultCfg = Configuration False

-- | Use this 'Configuration' when debugging the library
debugCfg :: Configuration
debugCfg = Configuration True

-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
parseScoped :: BSL.ByteString -> Either ParseError (Program TyName Name AlexPosn)
parseScoped str = fmap (\(p, s) -> rename s p) $ runExcept $ runStateT (parseST str) emptyIdentifierState

programType :: Natural -- ^ Gas provided to typechecker
            -> TypeState a
            -> Program TyNameWithKind NameWithType a
            -> Either (TypeError a) (RenamedType ())
programType n (TypeState _ tys) (Program _ _ t) = runTypeCheckM i n $ typeOf t
    where i = maybe 0 (fst . fst) (IM.maxViewWithKey tys)

formatDoc :: BSL.ByteString -> Either ParseError (Doc a)
formatDoc = fmap pretty . parse

format :: Configuration -> BSL.ByteString -> Either ParseError T.Text
format (Configuration True)  = fmap (render . debug) . parseScoped
format (Configuration False) = fmap render . formatDoc

discardAnnsName :: Name a -> Name ()
discardAnnsName n = n { nameAttribute = () }

discardAnnsTyName :: TyName a -> TyName ()
discardAnnsTyName = TyName . discardAnnsName . unTyName

discardAnnsKind :: Kind a -> Kind ()
discardAnnsKind = cata f
    where
        f :: KindF a (Kind ()) -> Kind ()
        f(TypeF _)     = Type ()
        f(KindArrowF _ k k')        = KindArrow () k k'
        f(SizeF _)     = Size ()

discardAnnsTy :: forall a . Type TyName a -> Type TyName ()
discardAnnsTy = cata f
    where
        f :: TypeF TyName a (Type TyName ()) -> Type TyName ()
        f(TyAppF _ t t')     = TyApp () t t'
        f(TyVarF _ n)        = TyVar () (discardAnnsTyName n)
        f(TyFunF _ t t')     = TyFun () t t'
        f(TyFixF _ n t)      = TyFix () (discardAnnsTyName n) t
        f(TyForallF _ n k t) = TyForall () (discardAnnsTyName n) (discardAnnsKind k) t
        f(TyBuiltinF _ n)    = TyBuiltin () n
        f(TyIntF _ n)        = TyInt () n
        f(TyLamF _ n k t)    = TyLam () (discardAnnsTyName n) (discardAnnsKind k) t

discardAnnsTerm :: forall a . Term TyName Name a -> Term TyName Name ()
discardAnnsTerm = cata f
    where
        f :: TermF TyName Name a (Term TyName Name ()) -> Term TyName Name ()
        f(VarF _ n)         = Var () (discardAnnsName n)
        f(TyAbsF _ n k t)   = TyAbs () (discardAnnsTyName n) (discardAnnsKind k) t
        f(LamAbsF _ n ty t) = LamAbs () (discardAnnsName n) (discardAnnsTy ty) t
        f(ApplyF _ t t')    = Apply () t t'
        f(ConstantF _ c)    = Constant () (discardAnnsConstant c)
        f(TyInstF _ t ty)   = TyInst () t (discardAnnsTy ty)
        f(UnwrapF _ t)      = Unwrap () t
        f(WrapF _ tn ty t)  = Wrap () (discardAnnsTyName tn) (discardAnnsTy ty) t
        f(ErrorF _ ty)      = Error () (discardAnnsTy ty)

discardAnnsConstant :: Constant a -> Constant ()
discardAnnsConstant = \case
    BuiltinInt _ n i -> BuiltinInt () n i
    BuiltinBS _ n bs -> BuiltinBS () n bs
    BuiltinSize _ n -> BuiltinSize () n
    BuiltinName _ n -> BuiltinName () n
