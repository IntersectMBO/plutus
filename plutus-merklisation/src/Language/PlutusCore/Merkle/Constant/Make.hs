-- | Smart constructors of PLC constants.

{-# LANGUAGE GADTs #-}

module Language.PlutusCore.Merkle.Constant.Make
    ( builtinNameAsTerm
    , dynamicBuiltinNameAsTerm
    , makeIntConstant
    , makeBuiltinInt
    , makeBuiltinBS
    , makeBuiltinStr
    ) where

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Core

import qualified Data.ByteString.Lazy      as BSL

-- | Lift a 'BuiltinName' to 'Term'.
builtinNameAsTerm :: TermLike term tyname name => BuiltinName -> term Integer
builtinNameAsTerm = builtin (-1) . BuiltinName (-1)

-- | Lift a 'DynamicBuiltinName' to 'Term'.
dynamicBuiltinNameAsTerm :: TermLike term tyname name => DynamicBuiltinName -> term Integer
dynamicBuiltinNameAsTerm = builtin (-1) . DynBuiltinName (-1)

-- | Convert a Haskell 'Integer' to the corresponding PLC @integer@.
makeIntConstant
    :: TermLike term tyname name
    => Integer        -- ^ An 'Integer' to lift.
    -> term Integer
makeIntConstant intVal = constant (-1) $ BuiltinInt (-1) intVal

-- | Convert a Haskell 'Integer' to the corresponding PLC @integer@.
makeBuiltinInt :: Integer -> Constant Integer
makeBuiltinInt = BuiltinInt (-1)

-- | Convert a Haskell 'ByteString' to the corresponding PLC @bytestring@.
makeBuiltinBS :: BSL.ByteString -> Constant Integer
makeBuiltinBS = BuiltinBS (-1)

-- | Convert a Haskell 'String' to the corresponding PLC @string@.
makeBuiltinStr :: String -> Constant Integer
makeBuiltinStr = BuiltinStr (-1)
