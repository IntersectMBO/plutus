-- | Smart constructors of PLC constants.

{-# LANGUAGE GADTs #-}

module Language.PlutusCore.Constant.Make
    ( builtinNameAsTerm
    , dynamicBuiltinNameAsTerm
    , makeAutoSizedBuiltinInt
    , makeAutoSizedBuiltinBS
    , makeDynBuiltinInt
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

-- | Make a 'Constant' out of an 'Integer'.
makeAutoSizedBuiltinInt :: Integer -> Constant ()
makeAutoSizedBuiltinInt = BuiltinInt ()

-- | Make a 'Constant' out of a 'ByteString'.
makeAutoSizedBuiltinBS :: BSL.ByteString -> Constant ()
makeAutoSizedBuiltinBS = BuiltinBS ()

{- Note [Dynamic sized built-ins]
How do we increment an integer in PLC? We can't simply write @addInteger {s} i 1@, because @1@
is not even legal syntax. The legal syntax is @1!1@ where the right @1@ is an integer and the left
@1@ is its size. In order for two integers to be addable, they have to be of the same type, so
we can't simply write @addInteger {s} i 1!1@, because @1!1@ is not of type @integer s@
(unless @s@ is literally @1@). Hence we need to resize @1!1@. The final solution is

> addInteger {s} i (resizeInteger {1} {s} ss 1!1)

Constructing such terms by hand is tedious and error-prone, therefore we define the
'makeDynBuiltinInt' function, which computes the size of an @Integer@, constructs the
corresponding built-in @integer@ and applies appropriately instantiated 'resizeInteger'
to the result.

Same considerations apply to bytestrings.
-}

-- | Convert a Haskell 'Integer' to the corresponding PLC @integer@.
makeDynBuiltinInt
    :: TermLike term tyname name
    => Integer        -- ^ An 'Integer' to lift.
    -> term ()
makeDynBuiltinInt intVal = constant () $ BuiltinInt () intVal

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
