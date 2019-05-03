-- | Smart constructors of PLC constants.

{-# LANGUAGE GADTs #-}

module Language.PlutusCore.Constant.Make
    ( builtinNameAsTerm
    , dynamicBuiltinNameAsTerm
    , makeIntConstant
    , makeBuiltinInt
    , makeBuiltinBS
    , makeBuiltinStr
    ) where

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Type

import qualified Data.ByteString.Lazy      as BSL

-- | Lift a 'BuiltinName' to 'Term'.
builtinNameAsTerm :: TermLike term tyname name => BuiltinName -> term ()
builtinNameAsTerm = builtin () . BuiltinName ()

-- | Lift a 'DynamicBuiltinName' to 'Term'.
dynamicBuiltinNameAsTerm :: TermLike term tyname name => DynamicBuiltinName -> term ()
dynamicBuiltinNameAsTerm = builtin () . DynBuiltinName ()

-- | Convert a Haskell 'Integer' to the corresponding PLC @integer@.
makeIntConstant
    :: TermLike term tyname name
    => Integer        -- ^ An 'Integer' to lift.
    -> term ()
makeIntConstant intVal = constant () $ BuiltinInt () intVal

-- | Convert a Haskell 'Integer' to the corresponding PLC @integer@.
makeBuiltinInt :: Integer -> Constant ()
makeBuiltinInt = BuiltinInt ()

-- | Convert a Haskell 'ByteString' to the corresponding PLC @bytestring@.
makeBuiltinBS :: BSL.ByteString -> Constant ()
makeBuiltinBS = BuiltinBS ()

-- | Convert a Haskell 'String' to the corresponding PLC @string@.
makeBuiltinStr :: String -> Constant ()
makeBuiltinStr = BuiltinStr ()
