-- | Smart constructors of PLC constants.

{-# LANGUAGE GADTs #-}

module Language.PlutusCore.Erasure.Untyped.Constant.Make
    ( builtinNameAsTerm
    , dynamicBuiltinNameAsTerm
    , makeIntConstant
    , makeBuiltinInt
    , makeBuiltinBS
    , makeBuiltinStr
    ) where

import qualified Language.PlutusCore.Core                  as PLC
import           Language.PlutusCore.Erasure.Untyped.MkPlc
import           Language.PlutusCore.Erasure.Untyped.Term

import qualified Data.ByteString.Lazy                      as BSL

-- | Lift a 'BuiltinName' to 'Term'.
builtinNameAsTerm :: TermLike term name => PLC.BuiltinName -> term ()
builtinNameAsTerm = builtin () . BuiltinName ()

-- | Lift a 'DynamicBuiltinName' to 'Term'.
dynamicBuiltinNameAsTerm :: TermLike term name => PLC.DynamicBuiltinName -> term ()
dynamicBuiltinNameAsTerm = builtin () . DynBuiltinName ()

-- | Convert a Haskell 'Integer' to the corresponding PLC @integer@.
makeIntConstant
    :: TermLike term name
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
