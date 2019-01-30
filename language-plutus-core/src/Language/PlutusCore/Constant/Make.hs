-- | Smart constructors of PLC constants.

{-# LANGUAGE GADTs #-}

module Language.PlutusCore.Constant.Make
    ( builtinNameAsTerm
    , dynamicBuiltinNameAsTerm
    , toBoundsInt
    , toInclusiveBoundsInt
    , checkBoundsInt
    , checkBoundsBS
    , sizeOfInteger
    , sizeOfByteString
    , makeAutoSizedBuiltinInt
    , makeAutoSizedBuiltinBS
    , makeDynBuiltinInt
    , makeDynBuiltinIntSizedAs
    , makeBuiltinInt
    , makeBuiltinBS
    , makeBuiltinStr
    , makeSizedConstant
    , makeBuiltinBool
    , makeBuiltin
    , unsafeMakeBuiltin
    , unsafeMakeDynamicBuiltin
    , makeSizedConstantNOCHECK
    , makeBuiltinNOCHECK
    ) where

import           Language.PlutusCore.Constant.Dynamic.Pretty
import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Data.Bits                                   (bit)
import qualified Data.ByteString.Lazy                        as BSL
import           Data.Maybe

-- | Lift a 'BuiltinName' to 'Term'.
builtinNameAsTerm :: BuiltinName -> Term tyname name ()
builtinNameAsTerm = Builtin () . BuiltinName ()

-- | Lift a 'DynamicBuiltinName' to 'Term'.
dynamicBuiltinNameAsTerm :: DynamicBuiltinName -> Term tyname name ()
dynamicBuiltinNameAsTerm = Builtin () . DynBuiltinName ()

-- | Return the @[-2^(8s - 1), 2^(8s - 1))@ bounds for integers of a given 'Size'.
toBoundsInt :: Size -> (Integer, Integer)
toBoundsInt s = (-b, b) where
    b = bit (8 * fromIntegral s - 1)  -- This is much quicker than 2^n for large n

-- | Return the @[-2^(8s - 1), 2^(8s - 1) - 1]@ bounds for integers of a given 'Size'.
toInclusiveBoundsInt :: Size -> (Integer, Integer)
toInclusiveBoundsInt = fmap pred . toBoundsInt

-- | Check whether an 'Integer' is in the @[-2^(8s - 1), 2^(8s - 1))@ interval.
checkBoundsInt :: Size -> Integer -> Bool
checkBoundsInt s i = s /= 0 && low <= i && i < high where
    (low, high) = toBoundsInt s

-- | Check whether the length of a 'ByteString' is less than or equal to a given 'Size'.
checkBoundsBS :: Size -> BSL.ByteString -> Bool
checkBoundsBS size bs = BSL.length bs <= fromIntegral size

-- | Compute the size of an 'Integer'. See also 'toBoundsInt'.
sizeOfInteger :: Integer -> Size
sizeOfInteger i = fromIntegral $ ilogRound 2 (abs i + d) `div` 8 + 1 where
    d = if i < 0 then 0 else 1

-- | Compute the size of a 'ByteString'. See also 'toBoundsBS'.
sizeOfByteString :: BSL.ByteString -> Size
sizeOfByteString = fromIntegral . BSL.length

-- | Make a 'Constant' out of an 'Integer'. The size is computed using 'sizeOfInteger'.
makeAutoSizedBuiltinInt :: Integer -> Constant ()
makeAutoSizedBuiltinInt i = BuiltinInt () (sizeOfInteger i) i

-- | Make a 'Constant' out of a 'ByteString'. The size is computed using 'sizeOfBS'.
makeAutoSizedBuiltinBS :: BSL.ByteString -> Constant ()
makeAutoSizedBuiltinBS bs = BuiltinBS () (sizeOfByteString bs) bs

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
    :: Type tyname ()       -- ^ An actual size @s@.
    -> Term tyname name ()  -- ^ A singleton for @s@.
    -> Integer              -- ^ An 'Integer' to lift.
    -> Term tyname name ()
makeDynBuiltinInt sTy sTerm intVal =
    mkIterApp () (mkIterInst () resizeInteger [TyInt () sizeOfIntVal, sTy]) [sTerm, intTerm] where
        sizeOfIntVal = sizeOfInteger intVal
        resizeInteger = builtinNameAsTerm ResizeInteger
        intTerm = Constant () $ BuiltinInt () sizeOfIntVal intVal

-- | Convert a Haskell 'Integer' to the corresponding PLC @integer@,
-- taking the size singleton from an already existing PLC @integer@.
makeDynBuiltinIntSizedAs
    :: Type tyname ()       -- ^ An actual size @s@.
    -> Term tyname name ()  -- ^ An @integer@ to take the singleton size from.
    -> Integer              -- ^ An 'Integer' to lift.
    -> Term tyname name ()
makeDynBuiltinIntSizedAs sTy intAs = makeDynBuiltinInt sTy sTerm where
    sTerm = Apply () (TyInst () (builtinNameAsTerm SizeOfInteger) sTy) intAs

-- | Check whether an 'Integer' is in bounds (see 'checkBoundsInt') and return it as a 'Constant'.
makeBuiltinInt :: Size -> Integer -> Maybe (Constant ())
makeBuiltinInt size int = checkBoundsInt size int ? BuiltinInt () size int

-- | Check whether a 'ByteString' is in bounds (see 'checkBoundsBS') and return it as a 'Constant'.
makeBuiltinBS :: Size -> BSL.ByteString -> Maybe (Constant ())
makeBuiltinBS size bs = checkBoundsBS size bs ? BuiltinBS () size bs

makeBuiltinStr :: String -> Constant ()
makeBuiltinStr = BuiltinStr ()

-- | Convert a Haskell value to the corresponding PLC constant indexed by size
-- checking all constraints (e.g. an 'Integer' is in appropriate bounds) along the way.
makeSizedConstant :: Size -> TypedBuiltinSized a -> a -> Maybe (Constant ())
makeSizedConstant size TypedBuiltinSizedInt  int = makeBuiltinInt size int
makeSizedConstant size TypedBuiltinSizedBS   bs  = makeBuiltinBS  size bs
makeSizedConstant size TypedBuiltinSizedSize ()  = Just $ BuiltinSize () size

-- | Convert a 'Bool' to the corresponding PLC's @boolean@.
makeBuiltinBool :: Bool -> Term TyName Name ()
makeBuiltinBool b = if b then true else false

-- | Convert a Haskell value to the corresponding PLC value checking all constraints
-- (e.g. an 'Integer' is in appropriate bounds) along the way.
makeBuiltin :: TypedBuiltinValue Size a -> Maybe (Term TyName Name ())
makeBuiltin (TypedBuiltinValue tb x) = case tb of
    TypedBuiltinSized se tbs -> Constant () <$> makeSizedConstant (flattenSizeEntry se) tbs x
    TypedBuiltinBool         -> Just $ makeBuiltinBool x
    TypedBuiltinDyn          -> makeDynamicBuiltin x

-- | Convert a Haskell value to a PLC value checking all constraints
-- (e.g. an 'Integer' is in appropriate bounds) along the way and
-- fail in case constraints are not satisfied.
unsafeMakeBuiltin :: PrettyDynamic a => TypedBuiltinValue Size a -> Term TyName Name ()
unsafeMakeBuiltin tbv = fromMaybe err $ makeBuiltin tbv where
    err = error $ "unsafeMakeBuiltin: could not convert from a denotation: " ++ prettyString tbv

-- | Convert a Haskell value to a PLC value of a dynamic built-in type.
unsafeMakeDynamicBuiltin
    :: (KnownDynamicBuiltinType dyn, PrettyDynamic dyn) => dyn -> Term TyName Name ()
unsafeMakeDynamicBuiltin = unsafeMakeBuiltin . TypedBuiltinValue TypedBuiltinDyn

-- | Convert a Haskell value to the corresponding PLC constant indexed by size
-- without checking constraints (e.g. an 'Integer' is in appropriate bounds).
-- This function allows to fake a 'Constant' with a wrong size and thus it's highly unsafe
-- and should be used with great caution.
makeSizedConstantNOCHECK :: Size -> TypedBuiltinSized a -> a -> Constant ()
makeSizedConstantNOCHECK size TypedBuiltinSizedInt  int = BuiltinInt  () size int
makeSizedConstantNOCHECK size TypedBuiltinSizedBS   bs  = BuiltinBS   () size bs
makeSizedConstantNOCHECK size TypedBuiltinSizedSize ()  = BuiltinSize () size

-- | Convert a Haskell value to the corresponding PLC value without checking constraints
-- (e.g. an 'Integer' is in appropriate bounds).
-- This function allows to fake a 'Term' with a wrong size and thus it's highly unsafe
-- and should be used with great caution.
makeBuiltinNOCHECK :: PrettyDynamic a => TypedBuiltinValue Size a -> Term TyName Name ()
makeBuiltinNOCHECK tbv@(TypedBuiltinValue tb x) = case tb of
    TypedBuiltinSized se tbs -> Constant () $ makeSizedConstantNOCHECK (flattenSizeEntry se) tbs x
    TypedBuiltinBool         -> makeBuiltinBool x
    TypedBuiltinDyn          -> unsafeMakeBuiltin tbv
