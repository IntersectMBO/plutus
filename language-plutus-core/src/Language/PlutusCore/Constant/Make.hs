-- | Smart constructors of PLC constants.

{-# LANGUAGE GADTs #-}

module Language.PlutusCore.Constant.Make
    ( builtinNameAsTerm
    , dynamicBuiltinNameAsTerm
    , makeIntConstant
    , makeBuiltinInt
    , makeBuiltinBS
    , makeBuiltinStr
    , makeSizedConstant
    , makeBuiltin
    , unsafeMakeBuiltin
    , unsafeMakeDynamicBuiltin
    , makeBuiltinNOCHECK
    ) where

import           Language.PlutusCore.Constant.Dynamic.Pretty
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

import qualified Data.ByteString.Lazy                        as BSL

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

-- | Check whether an 'Integer' is in bounds (see 'checkBoundsInt') and return it as a 'Constant'.
makeBuiltinInt :: Integer -> Constant ()
makeBuiltinInt = BuiltinInt ()

-- | Check whether a 'ByteString' is in bounds (see 'checkBoundsBS') and return it as a 'Constant'.
makeBuiltinBS :: BSL.ByteString -> Constant ()
makeBuiltinBS = BuiltinBS ()

makeBuiltinStr :: String -> Constant ()
makeBuiltinStr = BuiltinStr ()

-- | Convert a Haskell value to the corresponding PLC constant indexed by size
-- checking all constraints (e.g. an 'Integer' is in appropriate bounds) along the way.
makeSizedConstant :: TypedBuiltinSized a -> a -> Constant ()
makeSizedConstant TypedBuiltinSizedInt  int = makeBuiltinInt int
makeSizedConstant TypedBuiltinSizedBS   bs  = makeBuiltinBS  bs

-- | Convert a Haskell value to the corresponding PLC value checking all constraints
-- (e.g. an 'Integer' is in appropriate bounds) along the way.
makeBuiltin :: TypedBuiltinValue a -> Maybe (Term TyName Name ())
makeBuiltin (TypedBuiltinValue tb x) = case tb of
    TypedBuiltinSized tbs -> Just $ Constant () $ makeSizedConstant tbs x
    TypedBuiltinDyn       -> makeDynamicBuiltin x

-- | Convert a Haskell value to a PLC value checking all constraints
-- (e.g. an 'Integer' is in appropriate bounds) along the way and
-- fail in case constraints are not satisfied.
unsafeMakeBuiltin :: PrettyDynamic a => TypedBuiltinValue a -> Term TyName Name ()
unsafeMakeBuiltin tbv = fromMaybe err $ makeBuiltin tbv where
    err = Prelude.error $ "unsafeMakeBuiltin: could not convert from a denotation: " ++ prettyString tbv

-- | Convert a Haskell value to a PLC value of a dynamic built-in type.
unsafeMakeDynamicBuiltin
    :: (KnownDynamicBuiltinType dyn, PrettyDynamic dyn) => dyn -> Term TyName Name ()
unsafeMakeDynamicBuiltin = unsafeMakeBuiltin . TypedBuiltinValue TypedBuiltinDyn

-- | Convert a Haskell value to the corresponding PLC value without checking constraints
-- (e.g. an 'Integer' is in appropriate bounds).
-- This function allows to fake a 'Term' with a wrong size and thus it's highly unsafe
-- and should be used with great caution.
makeBuiltinNOCHECK :: PrettyDynamic a => TypedBuiltinValue a -> Term TyName Name ()
makeBuiltinNOCHECK tbv@(TypedBuiltinValue tb x) = case tb of
    TypedBuiltinSized tbs -> Constant () $ makeSizedConstant tbs x
    TypedBuiltinDyn       -> unsafeMakeBuiltin tbv
