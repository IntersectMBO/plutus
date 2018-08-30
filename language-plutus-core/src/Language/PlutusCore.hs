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
    , prettyCfgText
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
    , BuiltinName (..)
    , TypeBuiltin (..)
    -- * Lexer
    , AlexPosn (..)
    -- * Formatting
    , format
    , formatDoc
    -- * Processing
    , annotate
    , annotateST
    , RenameError (..)
    , TyNameWithKind (..)
    , NameWithType (..)
    , TypeState (..)
    , RenamedType
    , RenamedTerm
    -- * Normalization
    , check
    , NormalizationError
    -- * Type synthesis
    , typeOf
    , kindOf
    , runTypeCheckM
    , programType
    , fileType
    , fileTypeCfg
    , printType
    , TypeError (..)
    , TypeCheckM
    , BuiltinTable (..)
    -- * Serialization
    , encodeProgram
    , decodeProgram
    , readProgram
    , writeProgram
    -- * Errors
    , PrettyCfg (..)
    , Error (..)
    , IsError (..)
    -- * Base functors
    , TermF (..)
    , TypeF (..)
    -- * CK Machine
    , CkEvalResult
    , runCk
    -- * Template Haskell
    , Size
    , Value
    , TypedBuiltinSized (..)
    , TypeScheme (..)
    , TypedBuiltin (..)
    , TypedBuiltinName (..)
    , TypedBuiltinValue (..)
    , eraseTypedBuiltinSized
    , toBoundsInt
    , PrimIterApp
    , IterApp (..)
    , makeConstant
    , flattenSizeEntry
    , ConstAppResult (..)
    , makeConstantApp
    , applyBuiltinName
    , typedAddInteger
    , typedSubtractInteger
    , typedMultiplyInteger
    , typedResizeInteger
    , typedConcatenate
    , typedResizeByteString
    , typedLessThanEqInteger
    , typedGreaterThanEqInteger
    , typedTakeByteString
    , typedDropByteString
    , typedEqByteString
    , typedEqInteger
    , typedDivideInteger
    , typedRemainderInteger
    , typedLessThanInteger
    , typedGreaterThanInteger
    , Quote
    , runQuote
    -- * Name generation
    , freshUnique
    , freshName
    , freshTyName
    -- * Quasi-Quoters
    , plcType
    , plcTerm
    , plcProgram
    ) where

import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.ByteString.Lazy              as BSL
import qualified Data.IntMap                       as IM
import qualified Data.Text                         as T
import           Data.Text.Prettyprint.Doc         hiding (annotate)
import           Language.PlutusCore.CBOR
import           Language.PlutusCore.CkMachine
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Error
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Parser
import           Language.PlutusCore.PrettyCfg
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.TH
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeSynthesis
import           PlutusPrelude


-- | Given a file at @fibonacci.plc@, @fileType "fibonacci.plc"@ will display
-- its type or an error message.
fileType :: FilePath -> IO T.Text
fileType = fmap (either prettyCfgText id . printType) . BSL.readFile

-- | Given a file, display
-- its type or an error message, optionally dumping annotations and debug
-- information.
fileTypeCfg :: Configuration -> FilePath -> IO T.Text
fileTypeCfg cfg = fmap (either (renderCfg cfg) id . printType) . BSL.readFile

-- | Print the type of a program contained in a 'ByteString'
printType :: BSL.ByteString -> Either (Error AlexPosn) T.Text
printType = collectErrors . fmap (convertError . typeErr <=< convertError . annotateST) . parseScoped

typeErr :: (TypeState a, Program TyNameWithKind NameWithType a) -> Either (TypeError a) T.Text
typeErr = fmap prettyCfgText . uncurry (programType 10000)

-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
parseScoped :: BSL.ByteString -> Either (ParseError AlexPosn) (Program TyName Name AlexPosn)
parseScoped str = fmap (\(p, s) -> rename s p) $ runExcept $ runStateT (parseST str) emptyIdentifierState

programType :: Natural -- ^ Gas provided to typechecker
            -> TypeState a
            -> Program TyNameWithKind NameWithType a
            -> Either (TypeError a) (RenamedType ())
programType n (TypeState _ tys) (Program _ _ t) = runTypeCheckM i n $ typeOf t
    where i = maybe 0 (fst . fst) (IM.maxViewWithKey tys)

formatDoc :: BSL.ByteString -> Either (ParseError AlexPosn) (Doc a)
formatDoc = fmap (prettyCfg defaultCfg) . parse

format :: Configuration -> BSL.ByteString -> Either (ParseError AlexPosn) T.Text
format cfg = fmap (render . prettyCfg cfg) . parseScoped
