{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusCore.Generators.PIR.Builtin where

import Data.ByteString (ByteString)
import Data.Coerce
import Data.Int
import Data.Kind qualified as GHC
import Data.Proxy
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Test.QuickCheck

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Data

instance Arbitrary Data where
    arbitrary = error "implement me"
    shrink = error "implement me"

-- | Same as 'Arbitrary' but specifically for Plutus built-in types, so that we are not tied to
-- the default implementation of the methods for a built-in type.
class ArbitraryBuiltin a where
    arbitraryBuiltin :: Gen a
    default arbitraryBuiltin :: Arbitrary a => Gen a
    arbitraryBuiltin = arbitrary

    shrinkBuiltin :: a -> [a]
    default shrinkBuiltin :: Arbitrary a => a -> [a]
    shrinkBuiltin = shrink

instance ArbitraryBuiltin ()
instance ArbitraryBuiltin Bool
instance ArbitraryBuiltin Data

-- | The 'Arbitrary' instance for 'Integer' only generates small integers:
--
-- >>> :set -XTypeApplications
-- >>> fmap (any ((> 30) . abs) . concat . concat . concat) . sample' $ arbitrary @[[[Integer]]]
-- False
--
-- We want to at least occasionally generate some larger ones, which is what the 'Arbitrary'
-- instance for 'Int64' does:
--
-- >>> import Data.Int
-- >>> fmap (any ((> 10000) . abs) . concat . concat . concat) . sample' $ arbitrary @[[[Int64]]]
-- True
instance ArbitraryBuiltin Integer where
    arbitraryBuiltin = frequency
        [ (4, arbitrary @Integer)
        , (1, fromIntegral <$> arbitrary @Int64)
        ]

instance ArbitraryBuiltin Text where
    arbitraryBuiltin = Text.pack . getPrintableString <$> arbitrary
    shrinkBuiltin = map (Text.pack . getPrintableString) . shrink . PrintableString . Text.unpack

instance ArbitraryBuiltin ByteString where
    arbitraryBuiltin = Text.encodeUtf8 <$> arbitraryBuiltin
    shrinkBuiltin = map Text.encodeUtf8 . shrinkBuiltin . Text.decodeUtf8

-- | For providing an 'Arbitrary' instance deferring to 'ArbitraryBuiltin'. Useful for implementing
-- 'ArbitraryBuiltin' for a polymorphic built-in type by taking the logic for handling spines from
-- the 'Arbitrary' class and the logic for handling elements from 'ArbitraryBuiltin'.
newtype AsArbitraryBuiltin a = AsArbitraryBuiltin
    { unAsArbitraryBuiltin :: a
    } deriving newtype (Show)

instance ArbitraryBuiltin a => Arbitrary (AsArbitraryBuiltin a) where
    arbitrary = coerce $ arbitraryBuiltin @a
    shrink = coerce $ shrinkBuiltin @a

-- We could do this and the next one generically using 'ElaborateBuiltin', but it would be more
-- code, so we keep it simple.
instance ArbitraryBuiltin a => ArbitraryBuiltin [a] where
    arbitraryBuiltin = coerce $ arbitrary @[AsArbitraryBuiltin a]
    shrinkBuiltin = coerce $ shrink @[AsArbitraryBuiltin a]

instance (ArbitraryBuiltin a, ArbitraryBuiltin b) => ArbitraryBuiltin (a, b) where
    arbitraryBuiltin = coerce $ arbitrary @(AsArbitraryBuiltin a, AsArbitraryBuiltin b)
    shrinkBuiltin = coerce $ shrink @(AsArbitraryBuiltin a, AsArbitraryBuiltin b)

-- | Either a fail to generate anything or a built-in type of a given kind.
data MaybeSomeTypeOf k
    = NothingSomeType
    | forall (a :: k). JustSomeType (DefaultUni (Esc a))

-- | Generate a 'DefaultUniApply' if possible.
genDefaultUniApply :: KnownKind k => Gen (MaybeSomeTypeOf k)
genDefaultUniApply = do
    mayFun <- scale (`div` 2) arbitrary
    mayArg <- scale (`div` 2) arbitrary :: Gen (MaybeSomeTypeOf GHC.Type)
    pure $ case (mayFun, mayArg) of
        (JustSomeType fun, JustSomeType arg) -> JustSomeType $ fun `DefaultUniApply` arg
        _                                    -> NothingSomeType

-- | Shrink a 'DefaultUniApply' to one of the elements of the spine and throw away the head
-- (because the head of an application can't be of the same kind as the whole application).
-- We don't have higher-kinded built-in types, so we don't do this kind of shrinking for any kinds
-- other than *.
shrinkDefaultUniApplyStar :: DefaultUni (Esc b) -> [MaybeSomeTypeOf GHC.Type]
shrinkDefaultUniApplyStar (fun `DefaultUniApply` arg) =
    [JustSomeType arg | SingType <- [toSingKind arg]] ++ shrinkDefaultUniApplyStar fun
shrinkDefaultUniApplyStar _ = []

instance KnownKind k => Arbitrary (MaybeSomeTypeOf k) where
   arbitrary = do
       size <- getSize
       oneof $ case knownKind @k of
           SingType ->
               [genDefaultUniApply | size > 10] ++
               [ pure $ JustSomeType DefaultUniInteger
               , pure $ JustSomeType DefaultUniByteString
               , pure $ JustSomeType DefaultUniString
               , pure $ JustSomeType DefaultUniUnit
               , pure $ JustSomeType DefaultUniBool
               -- Commented out, because the 'Arbitrary' instance for 'Data' isn't implemented
               -- (errors out).
               -- , pure $ JustSomeType DefaultUniData
               ]
           SingType `SingKindArrow` SingType ->
               [genDefaultUniApply | size > 10] ++
               [pure $ JustSomeType DefaultUniProtoList]
           SingType `SingKindArrow` SingType `SingKindArrow` SingType ->
               -- No 'genDefaultUniApply', because we don't have any built-in type constructors
               -- taking three or more arguments.
               [pure $ JustSomeType DefaultUniProtoPair]
           _ -> [pure NothingSomeType]

   -- No shrinks if you don't have anything to shrink.
   shrink NothingSomeType    = []
   shrink (JustSomeType uni) =
       case knownKind @k of
           SingType -> case uni of
               -- 'DefaultUniUnit' is the "minimal" built-in type, can't shrink it any further.
               DefaultUniUnit -> []
               -- Any other built-in type of kind * shrinks to 'DefaultUniUnit' and if it happens to
               -- be a built-in type application, then also all suitable arguments of the
               -- application.
               _              -> JustSomeType DefaultUniUnit : shrinkDefaultUniApplyStar uni
           -- No suitable builtins to shrink to for non-* kinds.
           _ -> []

-- | Convert a @MaybeSomeTypeOf kind@ to a @Maybe (SomeTypeIn DefaultUni)@ and forget the @kind@
-- (which was only used for generating well-kinded built-in type applications, which we have to do
-- due to having intrinsic kinding of builtins).
fromMaybeSomeTypeOf :: MaybeSomeTypeOf kind -> Maybe (SomeTypeIn DefaultUni)
fromMaybeSomeTypeOf NothingSomeType    = Nothing
fromMaybeSomeTypeOf (JustSomeType uni) = Just $ SomeTypeIn uni

-- | Generate a built-in type of a given kind.
genBuiltinTypeOf :: Kind () -> Gen (Maybe (SomeTypeIn DefaultUni))
genBuiltinTypeOf kind =
    withKnownKind kind $ \(_ :: Proxy kind) ->
        fromMaybeSomeTypeOf <$> arbitrary @(MaybeSomeTypeOf kind)
