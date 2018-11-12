{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}

module Language.PlutusCore.Lexer.Type ( BuiltinName (..)
                                      , DynamicBuiltinType (..)
                                      , DynamicBuiltinName (..)
                                      , StagedBuiltinName (..)
                                      , Version (..)
                                      , Keyword (..)
                                      , Special (..)
                                      , Token (..)
                                      , TypeBuiltin (..)
                                      , prettyBytes
                                      , allBuiltinNames
                                      ) where

import           Language.PlutusCore.Name
import           PlutusPrelude

import qualified Data.ByteString.Lazy               as BSL
import qualified Data.Text                          as T
import           Data.Text.Encoding                 (decodeUtf8)
import           Data.Text.Prettyprint.Doc.Internal (Doc (Text))
import           Language.Haskell.TH.Syntax         (Lift)
import           Numeric                            (showHex)

-- | A builtin type
data TypeBuiltin = TyByteString
                 | TyInteger
                 | TySize
                 | DynBuiltinType DynamicBuiltinType
                 deriving (Show, Eq, Ord, Generic, NFData, Lift)

-- | Builtin functions
data BuiltinName = AddInteger
                 | SubtractInteger
                 | MultiplyInteger
                 | DivideInteger
                 | QuotientInteger
                 | RemainderInteger
                 | ModInteger
                 | LessThanInteger
                 | LessThanEqInteger
                 | GreaterThanInteger
                 | GreaterThanEqInteger
                 | EqInteger
                 | ResizeInteger
                 | IntToByteString
                 | Concatenate
                 | TakeByteString
                 | DropByteString
                 | ResizeByteString
                 | SHA2
                 | SHA3
                 | VerifySignature
                 | EqByteString
                 | TxHash
                 | BlockNum
                 -- See Note [sizeOfInteger].
                 | SizeOfInteger
                 deriving (Show, Eq, Ord, Enum, Bounded, Generic, NFData, Lift)

{- Note [sizeOfInteger]
The 'sizeOfInteger' built-in is a later addition. The main motivation for adding it is that it
allows to pass fewer singleton sizes around. However less boilerplate is not the only advantage,
'sizeOfInteger' also allows to treat built-in functions and user-defined ones similarly.
Consider the 'addInteger' built-in: it has the following type signature (PLCish pseudocode):

    addInteger : forall s. integer s -> integer s -> integer s

We know that @integer s@ determines the @s@ and hence do not require an additional singleton size.
We could have @succInteger@ with a similar type signature:

    succInteger : forall s. integer s -> integer s

However without 'sizeOfInteger' we can't define 'succInteger' inside the language without requiring
an additional singleton size. A previous definition without 'sizeOfInteger':

    /\(s :: size) -> \(ss : size s) (i : integer s) ->
        addInteger {s} i (resizeInteger {1} {s} ss 1!1)

So we have this metaknowledge that @integer s@ determines the @s@, but without an additional primitive
cannot communicate this to Plutus Core and pay by passing a lot of sizes around. The current definition:

    /\(s :: size) -> \(i : integer s) ->
        addInteger {s} i (resizeInteger {1} {s} (sizeOfInteger {s} i) 1!1)

which has the desired type signature:

    succInteger : forall s. integer s -> integer s
-}

-- | The type of dynamic built-in types. I.e. types that exist on certain chains and do
-- not exist on others. Each 'DynamicBuiltinType' has an associated kind
-- this allows to kind check dynamic built-in types just like static ones.
newtype DynamicBuiltinType = DynamicBuiltinType
    { unDynamicBuiltinType :: T.Text  -- ^ The name of a dynamic built-in type.
    } deriving (Show, Eq, Ord, Generic)
      deriving newtype (NFData, Lift)

-- | The type of dynamic built-in functions. I.e. functions that exist on certain chains and do
-- not exist on others. Each 'DynamicBuiltinName' has an associated type and operational semantics --
-- this allows to type check and evaluate dynamic built-in names just like static ones.
newtype DynamicBuiltinName = DynamicBuiltinName
    { unDynamicBuiltinName :: T.Text  -- ^ The name of a dynamic built-in function.
    } deriving (Show, Eq, Ord, Generic)
      deriving newtype (NFData, Lift)

-- | Either a 'BuiltinName' (known statically) or a 'DynamicBuiltinName' (known dynamically).
data StagedBuiltinName = StaticStagedBuiltinName  BuiltinName
                       | DynamicStagedBuiltinName DynamicBuiltinName
                       deriving (Show, Eq, Generic, NFData, Lift)

-- | Version of Plutus Core to be used for the program.
data Version a = Version a Natural Natural Natural
               deriving (Show, Eq, Functor, Generic, NFData, Lift)

-- | A keyword in Plutus Core.
data Keyword = KwAbs
             | KwLam
             | KwFix
             | KwFun
             | KwAll
             | KwByteString
             | KwInteger
             | KwSize
             | KwType
             | KwProgram
             | KwCon
             | KwWrap
             | KwUnwrap
             | KwError
             deriving (Show, Eq, Generic, NFData)

-- | A special character. This type is only used internally between the lexer
-- and the parser.
data Special = OpenParen
             | CloseParen
             | OpenBracket
             | CloseBracket
             | Dot
             | Exclamation
             | OpenBrace
             | CloseBrace
             deriving (Show, Eq, Generic, NFData)

-- | A token generated by the lexer.
data Token a = LexName { loc        :: a
                       , name       :: BSL.ByteString
                       , identifier :: Unique -- ^ A 'Unique' assigned to the identifier during lexing.
                       }
             | LexInt { loc :: a, tkInt :: Integer }
             | LexBS { loc :: a, tkBytestring :: BSL.ByteString }
             | LexBuiltin { loc :: a, tkBuiltin :: BuiltinName }
             | LexNat { loc :: a, tkNat :: Natural }
             | LexKeyword { loc :: a, tkKeyword :: Keyword }
             | LexSpecial { loc :: a, tkSpecial :: Special }
             | EOF { loc :: a }
             deriving (Show, Eq, Generic, NFData)

asBytes :: Word8 -> Doc a
asBytes = Text 2 . T.pack . ($ mempty) . showHex

prettyBytes :: BSL.ByteString -> Doc a
prettyBytes b = "#" <> fold (asBytes <$> BSL.unpack b)
instance Pretty Special where
    pretty OpenParen    = "("
    pretty CloseParen   = ")"
    pretty OpenBracket  = "["
    pretty CloseBracket = "]"
    pretty Dot          = "."
    pretty Exclamation  = "!"
    pretty OpenBrace    = "{"
    pretty CloseBrace   = "}"

instance Pretty Keyword where
    pretty KwAbs        = "abs"
    pretty KwLam        = "lam"
    pretty KwFix        = "fix"
    pretty KwFun        = "fun"
    pretty KwAll        = "forall"
    pretty KwByteString = "bytestring"
    pretty KwInteger    = "integer"
    pretty KwSize       = "size"
    pretty KwType       = "type"
    pretty KwProgram    = "program"
    pretty KwCon        = "con"
    pretty KwWrap       = "wrap"
    pretty KwUnwrap     = "unwrap"
    pretty KwError      = "error"

instance Pretty (Token a) where
    pretty (LexName _ n _)   = pretty (decodeUtf8 (BSL.toStrict n))
    pretty (LexInt _ i)      = pretty i
    pretty (LexNat _ n)      = pretty n
    pretty (LexBS _ bs)      = prettyBytes bs
    pretty (LexBuiltin _ bn) = pretty bn
    pretty (LexKeyword _ kw) = pretty kw
    pretty (LexSpecial _ s)  = pretty s
    pretty EOF{}             = mempty

instance Pretty BuiltinName where
    pretty AddInteger           = "addInteger"
    pretty SubtractInteger      = "subtractInteger"
    pretty MultiplyInteger      = "multiplyInteger"
    pretty DivideInteger        = "divideInteger"
    pretty QuotientInteger      = "quotientInteger"
    pretty ModInteger           = "modInteger"
    pretty RemainderInteger     = "remainderInteger"
    pretty LessThanInteger      = "lessThanInteger"
    pretty LessThanEqInteger    = "lessThanEqualsInteger"
    pretty GreaterThanInteger   = "greaterThanInteger"
    pretty GreaterThanEqInteger = "greaterThanEqualsInteger"
    pretty EqInteger            = "equalsInteger"
    pretty ResizeInteger        = "resizeInteger"
    pretty IntToByteString      = "intToByteString"
    pretty Concatenate          = "concatenate"
    pretty TakeByteString       = "takeByteString"
    pretty DropByteString       = "dropByteString"
    pretty ResizeByteString     = "resizeByteString"
    pretty EqByteString         = "equalsByteString"
    pretty SHA2                 = "sha2_256"
    pretty SHA3                 = "sha3_256"
    pretty VerifySignature      = "verifySignature"
    pretty TxHash               = "txhash"
    pretty BlockNum             = "blocknum"
    pretty SizeOfInteger        = "sizeOfInteger"

instance Pretty DynamicBuiltinType where
    pretty (DynamicBuiltinType n) = pretty n

instance Pretty DynamicBuiltinName where
    pretty (DynamicBuiltinName n) = pretty n

instance Pretty StagedBuiltinName where
    pretty (StaticStagedBuiltinName  n) = pretty n
    pretty (DynamicStagedBuiltinName n) = pretty n

instance Pretty TypeBuiltin where
    pretty TyInteger                                = "integer"
    pretty TyByteString                             = "bytestring"
    pretty TySize                                   = "size"
    pretty (DynBuiltinType (DynamicBuiltinType ty)) = pretty ty

instance Pretty (Version a) where
    pretty (Version _ i j k) = pretty i <> "." <> pretty j <> "." <> pretty k

-- | The list of all 'BuiltinName's.
allBuiltinNames :: [BuiltinName]
allBuiltinNames = [minBound .. maxBound]
-- The way it's defined ensures that it's enough to add a new built-in to 'BuiltinName' and it'll be
-- automatically handled by tests and other stuff that deals with all built-in names at once.
