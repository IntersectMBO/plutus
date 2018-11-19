-- | This module assigns types to built-ins.
-- See the @plutus/language-plutus-core/docs/Constant application.md@
-- article for how this emerged.

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RankNTypes                #-}

module Language.PlutusCore.Constant.Typed
    ( BuiltinSized(..)
    , TypedBuiltinSized(..)
    , SizeEntry(..)
    , BuiltinType(..)
    , TypedBuiltin(..)
    , TypedBuiltinValue(..)
    , TypeScheme(..)
    , TypedBuiltinName(..)
    , DynamicBuiltinNameMeaning(..)
    , DynamicBuiltinNameDefinition(..)
    , DynamicBuiltinNameMeanings(..)
    , flattenSizeEntry
    , eraseTypedBuiltinSized
    , mapSizeEntryTypedBuiltin
    , mapSizeTypedBuiltin
    , closeTypedBuiltin
    , typedBuiltinSizedToType
    , withTypedBuiltinSized
    , withTypedBuiltin
    , typeSchemeResult
    , typedBuiltinToType
    , typeSchemeToType
    , dynamicBuiltinNameMeaningToType
    , insertDynamicBuiltinNameDefinition
    , withTypedBuiltinName
    , typeOfTypedBuiltinName
    , typeOfBuiltinName
    , typedAddInteger
    , typedSubtractInteger
    , typedMultiplyInteger
    , typedDivideInteger
    , typedQuotientInteger
    , typedModInteger
    , typedRemainderInteger
    , typedLessThanInteger
    , typedLessThanEqInteger
    , typedGreaterThanInteger
    , typedGreaterThanEqInteger
    , typedEqInteger
    , typedResizeInteger
    , typedIntToByteString
    , typedConcatenate
    , typedTakeByteString
    , typedDropByteString
    , typedSHA2
    , typedSHA3
    , typedVerifySignature
    , typedResizeByteString
    , typedEqByteString
    , typedTxHash
    , typedBlockNum
    , typedSizeOfInteger
    ) where

import           Language.PlutusCore.Constant.DynamicType
import           Language.PlutusCore.Lexer.Type           hiding (name)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.Type
import           PlutusPrelude

import qualified Data.ByteString.Lazy.Char8               as BSL
import           Data.GADT.Compare
import           Data.Map                                 (Map)
import qualified Data.Map                                 as Map
import qualified Data.Text.Encoding                       as Text

infixr 9 `TypeSchemeArrow`

-- | Built-in types indexed by @size@.
data BuiltinSized
    = BuiltinSizedInt
    | BuiltinSizedBS
    | BuiltinSizedSize
    deriving (Show, Eq)

-- | Built-in types indexed by @size@ along with their denotation.
data TypedBuiltinSized a where
    TypedBuiltinSizedInt  :: TypedBuiltinSized Integer
    TypedBuiltinSizedBS   :: TypedBuiltinSized BSL.ByteString
    -- See Note [Semantics of sizes].
    TypedBuiltinSizedSize :: TypedBuiltinSized ()

{- Note [Semantics of sizes]
We convert each PLC's @size s@ into Haskell's '()'. I.e. sizes are completely ignored in
the semantics of various built-ins. Hence the Haskell's type signature of PLC's 'resizeInteger' is

    () -> Integer -> Integer

while its PLC signature is

    forall s0 s1. size s1 -> integer s0 -> integer s1

This does not mean that we do not perform all the checks prescribed by the specification.
Merely that we can't compute using sizes on the Haskell side, e.g. we cannot assign a semantics to

    maxIntegerOfGivenSize : forall s. size s -> integer s

There are two reasons for that:

1. Clarity. We want to be clear that size checks are not handled by Haskell interpretations of
   Plutus Core built-ins -- they're handled separately (see the "Apply" module).
   The reason for that is that we do not basically care what an operation do w.r.t. to sizes,
   we only care whether something it returns fits into some expected size.
   And this last checking step can be performed uniformly for all currently presented built-ins.

2. The semantics of @integer s@ is 'Integer'. While this may look ok, we actually lose size information,
   so e.g. there is no meaningful way we could interpret

       sizeOfInteger : forall s. integer s -> size s

   with @size s@ being interpreted as 'Size', because in @Integer -> Size@ the size of the 'Integer'
   is not specified. And we can't compute it, because we want its actual runtime size rather than
   the minimal size it fits into, as the former can be larger than the latter.
   Hence the semantics we have is

       sizeOfIntegerMeaning :: Integer -> ()

   I.e. this doesn't do anything useful at all. But it's not supposed to,
   since it returns a size and sizes are handled separately as (1) describes.
-}

-- | Type-level sizes.
data SizeEntry size
    = SizeValue Size  -- ^ A constant size.
    | SizeBound size  -- ^ A bound size variable.
    deriving (Eq, Ord, Functor)
-- We write @SizeEntry Size@ sometimes, so this data type is not perfect, but it works fine.

-- | Built-in types.
data BuiltinType size
    = BuiltinSized (SizeEntry size) BuiltinSized
    | BuiltinBool

-- | Built-in types. A type is considired "built-in" if it can appear in the type signature
-- of a primitive operation. So @boolean@ is considered built-in even though it is defined in PLC
-- and is not primitive.
data TypedBuiltin size a where
    TypedBuiltinSized :: SizeEntry size -> TypedBuiltinSized a -> TypedBuiltin size a
    TypedBuiltinBool  :: TypedBuiltin size Bool
    TypedBuiltinDyn   :: KnownDynamicBuiltinType dyn => TypedBuiltin size dyn

-- | A 'TypedBuiltin' packaged together with a value of the type that the 'TypedBuiltin' denotes.
data TypedBuiltinValue size a = TypedBuiltinValue (TypedBuiltin size a) a

-- | Type schemes of primitive operations.
-- @a@ is the Haskell denotation of a PLC type represented as a 'TypeScheme'.
-- @r@ is the resulting type in @a@, e.g. the resulting type in
-- @ByteString -> Size -> Integer@ is @Integer@.
data TypeScheme size a r where
    TypeSchemeBuiltin :: TypedBuiltin size a -> TypeScheme size a a
    TypeSchemeArrow   :: TypeScheme size a q -> TypeScheme size b r -> TypeScheme size (a -> b) r
    TypeSchemeAllSize :: (size -> TypeScheme size a r) -> TypeScheme size a r
    -- This is nailed to @size@ rather than being a generic @TypeSchemeForall@ for simplicity
    -- and because at the moment we do not need anything else.
    -- We can make this generic by parametrising @TypeScheme@ by an
    -- @f :: Kind () -> *@ rather than @size@.

    -- The @r@ is rather ad hoc and needed only for tests.
    -- We could use type families to compute it instead of storing as an index.
    -- That's a TODO perhaps.

-- | A 'BuiltinName' with an associated 'TypeScheme'.
data TypedBuiltinName a r = TypedBuiltinName BuiltinName (forall size. TypeScheme size a r)
-- I attempted to unify various typed things, but sometimes type variables must be universally
-- quantified, sometimes they must be existentially quatified. And those are distinct type variables.

{- Note [DynamicBuiltinNameMeaning]
We represent the meaning of a 'DynamicBuiltinName' as a 'TypeScheme' and a Haskell denotation.
We need both while evaluting a 'DynamicBuiltinName', because 'TypeScheme' is required for
well-typedness to avoid using 'unsafeCoerce' and similar junk, while the denotation is what
actually computes. We do not need denotations for type checking, nor strongly typed 'TypeScheme'
is required, however analogously to static built-ins, we compute the types of dynamic built-ins from
their 'TypeScheme's. This way we only define a 'TypeScheme', which we anyway need, and then compute
the corresponding 'Type' from it. And we can't go the other way around -- from untyped to typed --
of course. Therefore a typed thing has to go before the corresponding untyped thing and in the
final pipeline one has to supply a 'DynamicBuiltinNameMeaning' for each of the 'DynamicBuiltinName's.
-}

-- | The meaning of a dynamic built-in name consists of its 'Type' represented as a 'TypeScheme'
-- and its Haskell denotation.
data DynamicBuiltinNameMeaning =
    forall a r. DynamicBuiltinNameMeaning (forall size. TypeScheme size a r) a
-- See the [DynamicBuiltinNameMeaning] note.

-- | The definition of a dynamic built-in consists of its name and meaning.
data DynamicBuiltinNameDefinition =
    DynamicBuiltinNameDefinition DynamicBuiltinName DynamicBuiltinNameMeaning

-- | Mapping from 'DynamicBuiltinName's to their 'DynamicBuiltinNameMeaning's.
newtype DynamicBuiltinNameMeanings = DynamicBuiltinNameMeanings
    { unDynamicBuiltinNameMeanings :: Map DynamicBuiltinName DynamicBuiltinNameMeaning
    } deriving (Semigroup, Monoid)

instance Pretty BuiltinSized where
    pretty BuiltinSizedInt  = "integer"
    pretty BuiltinSizedBS   = "bytestring"
    pretty BuiltinSizedSize = "size"

instance Pretty (TypedBuiltinSized a) where
    pretty = pretty . eraseTypedBuiltinSized

instance Pretty size => Pretty (SizeEntry size) where
    pretty (SizeValue size) = pretty size
    pretty (SizeBound size) = pretty size

instance Pretty size => Pretty (TypedBuiltin size a) where
    pretty (TypedBuiltinSized se tbs) = parens $ pretty tbs <+> pretty se
    pretty TypedBuiltinBool           = "bool"
    -- Do we want this entire thing to be 'PrettyBy' rather than 'Pretty'?
    -- This is just used in errors, so we probably do not care much.
    pretty dyn@TypedBuiltinDyn        = prettyPlcDef . runQuote $ getTypeEncoding dyn

instance (size ~ Size, PrettyDynamic a) => Pretty (TypedBuiltinValue size a) where
    pretty (TypedBuiltinValue (TypedBuiltinSized se _) x) = pretty se <+> "!" <+> prettyDynamic x
    pretty (TypedBuiltinValue TypedBuiltinBool         b) = prettyDynamic b
    pretty (TypedBuiltinValue TypedBuiltinDyn          x) = prettyDynamic x

liftOrdering :: Ordering -> GOrdering a a
liftOrdering LT = GLT
liftOrdering EQ = GEQ
liftOrdering GT = GGT

-- I tried using the 'dependent-sum-template' package,
-- but see https://stackoverflow.com/q/50048842/3237465
instance GEq TypedBuiltinSized where
    TypedBuiltinSizedInt  `geq` TypedBuiltinSizedInt  = Just Refl
    TypedBuiltinSizedBS   `geq` TypedBuiltinSizedBS   = Just Refl
    TypedBuiltinSizedSize `geq` TypedBuiltinSizedSize = Just Refl
    _                     `geq` _                     = Nothing

instance Eq size => GEq (TypedBuiltin size) where
    TypedBuiltinSized size1 tbs1 `geq` TypedBuiltinSized size2 tbs2 = do
        guard $ size1 == size2
        tbs1 `geq` tbs2
    TypedBuiltinBool             `geq` TypedBuiltinBool             = Just Refl
    -- A typed built-in is not equal to itself. TODO: do something about it.
    _                            `geq` _                            = Nothing

instance Ord size => GCompare (TypedBuiltin size) where
    TypedBuiltinSized size1 tbs1 `gcompare` TypedBuiltinSized size2 tbs2
        | Just Refl <- tbs1 `geq` tbs2 = liftOrdering $ size1 `compare` size2
        | otherwise                    = case (tbs1, tbs2) of
            (TypedBuiltinSizedInt , _                    ) -> GLT
            (TypedBuiltinSizedBS  , TypedBuiltinSizedInt ) -> GGT
            (TypedBuiltinSizedBS  , _                    ) -> GLT
            (TypedBuiltinSizedSize, _                    ) -> GGT
    TypedBuiltinBool             `gcompare` TypedBuiltinBool      = GEQ
    TypedBuiltinSized _ _        `gcompare` TypedBuiltinBool      = GLT
    TypedBuiltinBool             `gcompare` TypedBuiltinSized _ _ = GGT
    _                            `gcompare` _                     =
        error "Do not use me for comparing dynamic built-ins"

-- | Convert a 'TypedBuiltinSized' to its untyped counterpart.
eraseTypedBuiltinSized :: TypedBuiltinSized a -> BuiltinSized
eraseTypedBuiltinSized TypedBuiltinSizedInt  = BuiltinSizedInt
eraseTypedBuiltinSized TypedBuiltinSizedBS   = BuiltinSizedBS
eraseTypedBuiltinSized TypedBuiltinSizedSize = BuiltinSizedSize

-- | Extract the 'Size' from a 'SizeEntry'.
flattenSizeEntry :: SizeEntry Size -> Size
flattenSizeEntry (SizeValue size) = size
flattenSizeEntry (SizeBound size) = size

-- | Alter the 'SizeEntry' of a 'TypedBuiltin'.
mapSizeEntryTypedBuiltin
    :: (SizeEntry size -> SizeEntry size') -> TypedBuiltin size a -> TypedBuiltin size' a
mapSizeEntryTypedBuiltin f (TypedBuiltinSized se tbs) = TypedBuiltinSized (f se) tbs
mapSizeEntryTypedBuiltin _ TypedBuiltinBool           = TypedBuiltinBool
mapSizeEntryTypedBuiltin _ TypedBuiltinDyn            = TypedBuiltinDyn

-- | Alter the 'size' of a @TypedBuiltin size@.
mapSizeTypedBuiltin
    :: (size -> size') -> TypedBuiltin size a -> TypedBuiltin size' a
mapSizeTypedBuiltin = mapSizeEntryTypedBuiltin . fmap

-- | Map each 'SizeBound' to 'SizeValue'.
closeTypedBuiltin :: TypedBuiltin Size a -> TypedBuiltin b a
closeTypedBuiltin = mapSizeEntryTypedBuiltin $ SizeValue . flattenSizeEntry

-- | Convert a 'TypedBuiltinSized' to the corresponding 'TypeBuiltin' and
-- wrap the result in 'TyBuiltin' to get a 'Type'.
typedBuiltinSizedToType :: TypedBuiltinSized a -> Type TyName ()
typedBuiltinSizedToType TypedBuiltinSizedInt  = TyBuiltin () TyInteger
typedBuiltinSizedToType TypedBuiltinSizedBS   = TyBuiltin () TyByteString
typedBuiltinSizedToType TypedBuiltinSizedSize = TyBuiltin () TySize

-- | Apply a continuation to the typed version of a 'BuiltinSized'.
withTypedBuiltinSized :: BuiltinSized -> (forall a. TypedBuiltinSized a -> c) -> c
withTypedBuiltinSized BuiltinSizedInt  k = k TypedBuiltinSizedInt
withTypedBuiltinSized BuiltinSizedBS   k = k TypedBuiltinSizedBS
withTypedBuiltinSized BuiltinSizedSize k = k TypedBuiltinSizedSize

-- | Apply a continuation to the typed version of a 'Builtin'.
withTypedBuiltin :: BuiltinType size -> (forall a. TypedBuiltin size a -> c) -> c
withTypedBuiltin (BuiltinSized se b) k = withTypedBuiltinSized b $ k . TypedBuiltinSized se
withTypedBuiltin BuiltinBool         k = k TypedBuiltinBool

-- | The resulting 'TypedBuiltin' of a 'TypeScheme'.
typeSchemeResult :: TypeScheme () a r -> TypedBuiltin () r
typeSchemeResult (TypeSchemeBuiltin tb)   = tb
typeSchemeResult (TypeSchemeArrow _ schB) = typeSchemeResult schB
typeSchemeResult (TypeSchemeAllSize schK) = typeSchemeResult (schK ())

-- | Convert a 'TypedBuiltin' to the corresponding 'Type'.
typedBuiltinToType :: TypedBuiltin (Type TyName ()) a -> Quote (Type TyName ())
typedBuiltinToType (TypedBuiltinSized se tbs) =
    return . TyApp () (typedBuiltinSizedToType tbs) $ case se of
        SizeValue size -> TyInt () size
        SizeBound ty   -> ty
typedBuiltinToType TypedBuiltinBool           = getBuiltinBool
typedBuiltinToType dyn@TypedBuiltinDyn        = getTypeEncoding dyn

-- | Convert a 'TypeScheme' to the corresponding 'Type'.
-- Basically, a map from the PHOAS representation to the FOAS one.
typeSchemeToType :: TypeScheme (Type TyName ()) a r -> Quote (Type TyName ())
typeSchemeToType = go 0 where
    go :: Int -> TypeScheme (Type TyName ()) a r -> Quote (Type TyName ())
    go _ (TypeSchemeBuiltin tb)      = typedBuiltinToType tb
    go i (TypeSchemeArrow schA schB) =
        TyFun () <$> go i schA <*> go i schB
    go i (TypeSchemeAllSize schK)    = do
        s <- mapTyNameString (<> BSL.fromStrict (Text.encodeUtf8 $ prettyText i)) <$>
                freshTyName () "s"
        a <- go (succ i) . schK $ TyVar () s
        return $ TyForall () s (Size ()) a

-- | Extract the 'TypeScheme' from a 'DynamicBuiltinNameMeaning' and
-- convert it to the corresponding 'Type'.
dynamicBuiltinNameMeaningToType :: DynamicBuiltinNameMeaning -> Quote (Type TyName ())
dynamicBuiltinNameMeaningToType (DynamicBuiltinNameMeaning sch _) = typeSchemeToType sch

-- | Insert a 'DynamicBuiltinNameDefinition' into a 'DynamicBuiltinNameMeanings'.
insertDynamicBuiltinNameDefinition
    :: DynamicBuiltinNameDefinition -> DynamicBuiltinNameMeanings -> DynamicBuiltinNameMeanings
insertDynamicBuiltinNameDefinition
    (DynamicBuiltinNameDefinition name mean) (DynamicBuiltinNameMeanings nameMeans) =
        DynamicBuiltinNameMeanings $ Map.insert name mean nameMeans

-- | Apply a continuation to the typed version of a 'BuiltinName'.
withTypedBuiltinName :: BuiltinName -> (forall a r. TypedBuiltinName a r -> c) -> c
withTypedBuiltinName AddInteger           k = k typedAddInteger
withTypedBuiltinName SubtractInteger      k = k typedSubtractInteger
withTypedBuiltinName MultiplyInteger      k = k typedMultiplyInteger
withTypedBuiltinName DivideInteger        k = k typedDivideInteger
withTypedBuiltinName QuotientInteger      k = k typedQuotientInteger
withTypedBuiltinName RemainderInteger     k = k typedRemainderInteger
withTypedBuiltinName ModInteger           k = k typedModInteger
withTypedBuiltinName LessThanInteger      k = k typedLessThanInteger
withTypedBuiltinName LessThanEqInteger    k = k typedLessThanEqInteger
withTypedBuiltinName GreaterThanInteger   k = k typedGreaterThanInteger
withTypedBuiltinName GreaterThanEqInteger k = k typedGreaterThanEqInteger
withTypedBuiltinName EqInteger            k = k typedEqInteger
withTypedBuiltinName ResizeInteger        k = k typedResizeInteger
withTypedBuiltinName IntToByteString      k = k typedIntToByteString
withTypedBuiltinName Concatenate          k = k typedConcatenate
withTypedBuiltinName TakeByteString       k = k typedTakeByteString
withTypedBuiltinName DropByteString       k = k typedDropByteString
withTypedBuiltinName SHA2                 k = k typedSHA2
withTypedBuiltinName SHA3                 k = k typedSHA3
withTypedBuiltinName VerifySignature      k = k typedVerifySignature
withTypedBuiltinName ResizeByteString     k = k typedResizeByteString
withTypedBuiltinName EqByteString         k = k typedEqByteString
withTypedBuiltinName TxHash               k = k typedTxHash
withTypedBuiltinName BlockNum             k = k typedBlockNum
withTypedBuiltinName SizeOfInteger        k = k typedSizeOfInteger

-- | Return the 'Type' of a 'TypedBuiltinName'.
typeOfTypedBuiltinName :: TypedBuiltinName a r -> Quote (Type TyName ())
typeOfTypedBuiltinName (TypedBuiltinName _ scheme) = typeSchemeToType scheme

-- | Return the 'Type' of a 'BuiltinName'.
typeOfBuiltinName :: BuiltinName -> Quote (Type TyName ())
typeOfBuiltinName bn = withTypedBuiltinName bn typeOfTypedBuiltinName

sizeIntIntInt :: TypeScheme size (Integer -> Integer -> Integer) Integer
sizeIntIntInt =
    TypeSchemeAllSize $ \s ->
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt)

sizeIntIntBool :: TypeScheme size (Integer -> Integer -> Bool) Bool
sizeIntIntBool =
    TypeSchemeAllSize $ \s ->
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin TypedBuiltinBool

-- | Typed 'AddInteger'.
typedAddInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedAddInteger = TypedBuiltinName AddInteger sizeIntIntInt

-- | Typed 'SubtractInteger'.
typedSubtractInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedSubtractInteger = TypedBuiltinName SubtractInteger sizeIntIntInt

-- | Typed 'MultiplyInteger'.
typedMultiplyInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedMultiplyInteger = TypedBuiltinName MultiplyInteger sizeIntIntInt

-- | Typed 'DivideInteger'.
typedDivideInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedDivideInteger = TypedBuiltinName DivideInteger sizeIntIntInt

-- | Typed 'QuotientInteger'
typedQuotientInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedQuotientInteger = TypedBuiltinName QuotientInteger sizeIntIntInt

-- | Typed 'RemainderInteger'.
typedRemainderInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedRemainderInteger = TypedBuiltinName RemainderInteger sizeIntIntInt

-- | Typed 'ModInteger'
typedModInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedModInteger = TypedBuiltinName ModInteger sizeIntIntInt

-- | Typed 'LessThanInteger'.
typedLessThanInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedLessThanInteger = TypedBuiltinName LessThanInteger sizeIntIntBool

-- | Typed 'LessThanEqInteger'.
typedLessThanEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedLessThanEqInteger = TypedBuiltinName LessThanEqInteger sizeIntIntBool

-- | Typed 'GreaterThanInteger'.
typedGreaterThanInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedGreaterThanInteger = TypedBuiltinName GreaterThanInteger sizeIntIntBool

-- | Typed 'GreaterThanEqInteger'.
typedGreaterThanEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedGreaterThanEqInteger = TypedBuiltinName GreaterThanEqInteger sizeIntIntBool

-- | Typed 'EqInteger'.
typedEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedEqInteger = TypedBuiltinName EqInteger sizeIntIntBool

-- | Typed 'ResizeInteger'.
typedResizeInteger :: TypedBuiltinName (() -> Integer -> Integer) Integer
typedResizeInteger =
    TypedBuiltinName ResizeInteger $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedInt)

-- | Typed 'IntToByteString'.
typedIntToByteString :: TypedBuiltinName (() -> Integer -> BSL.ByteString) BSL.ByteString
typedIntToByteString =
    TypedBuiltinName IntToByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

-- | Typed 'Concatenate'.
typedConcatenate :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedConcatenate =
    TypedBuiltinName Concatenate $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS)

-- | Typed 'TakeByteString'.
typedTakeByteString :: TypedBuiltinName (Integer -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedTakeByteString =
    TypedBuiltinName TakeByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

-- | Typed 'DropByteString'.
typedDropByteString :: TypedBuiltinName (Integer -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedDropByteString =
    TypedBuiltinName DropByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

-- | Typed 'SHA2'.
typedSHA2 :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedSHA2 =
    TypedBuiltinName SHA2 $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 256) TypedBuiltinSizedBS)

-- | Typed 'SHA3'.
typedSHA3 :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedSHA3 =
    TypedBuiltinName SHA3 $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 256) TypedBuiltinSizedBS)

-- | Typed 'VerifySignature'.
typedVerifySignature :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> BSL.ByteString -> Bool) Bool
typedVerifySignature =
    TypedBuiltinName VerifySignature $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 -> TypeSchemeAllSize $ \s2 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s2) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin TypedBuiltinBool

-- | Typed 'ResizeByteString'.
typedResizeByteString :: TypedBuiltinName (() -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedResizeByteString =
    TypedBuiltinName ResizeByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

-- | Typed 'EqByteString'.
typedEqByteString :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> Bool) Bool
typedEqByteString =
    TypedBuiltinName EqByteString $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin TypedBuiltinBool

-- | Typed 'TxHash'.
typedTxHash :: TypedBuiltinName BSL.ByteString BSL.ByteString
typedTxHash =
    TypedBuiltinName TxHash $
        TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 256) TypedBuiltinSizedBS)

-- | Typed 'BlockNum'.
typedBlockNum :: TypedBuiltinName (() -> Integer) Integer
typedBlockNum =
    TypedBuiltinName BlockNum $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt)

-- | Typed 'SizeOfInteger'.
typedSizeOfInteger :: TypedBuiltinName (Integer -> ()) ()
typedSizeOfInteger =
    TypedBuiltinName SizeOfInteger $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedSize)
