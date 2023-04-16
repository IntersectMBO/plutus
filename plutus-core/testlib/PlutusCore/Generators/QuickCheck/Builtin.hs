{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusCore.Generators.QuickCheck.Builtin where

import PlutusCore hiding (Constr)
import PlutusCore.Builtin
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data
import PlutusCore.Generators.QuickCheck.Common (genList)

import Data.ByteString (ByteString)
import Data.Coerce
import Data.Int
import Data.Kind qualified as GHC
import Data.Maybe
import Data.Proxy
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Word
import Test.QuickCheck
import Test.QuickCheck.Instances.ByteString ()
import Universe

instance Arbitrary Data where
    arbitrary = sized genData

    shrink = genericShrink

genData :: Int -> Gen Data
genData depth =
    oneof $
        [genI, genB]
            <> [ genRec | depth > 1, genRec <-
                                        [ genListData (depth `div` 2)
                                        , genMapData (depth `div` 2)
                                        , genConstrData (depth `div` 2)
                                        ]
               ]
  where
    genI = I <$> arbitraryBuiltin
    genB = B <$> arbitraryBuiltin

genListWithMaxDepth :: Int -> (Int -> Gen a) -> Gen [a]
genListWithMaxDepth depth gen =
    -- The longer the list, the smaller the elements.
    frequency
        [ (100, genList 0 5 (gen depth))
        , (10, genList 0 50 (gen (depth `div` 2)))
        , (1, genList 0 500 (gen (depth `div` 4)))
        ]

genListData :: Int -> Gen Data
genListData depth = List <$> genListWithMaxDepth depth genData

genMapData :: Int -> Gen Data
genMapData depth =
    Map <$> genListWithMaxDepth depth (\d -> (,) <$> genData d <*> genData d)

genConstrData :: Int -> Gen Data
genConstrData depth =
    Constr
        <$> (fromIntegral <$> arbitrary @Word64)
        <*> genListWithMaxDepth depth genData

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

{- Note [QuickCheck and integral types]
The 'Arbitrary' instances for 'Integer' and 'Int64' only generate small integers:

    >>> :set -XTypeApplications
    >>> fmap (any ((> 30) . abs) . concat . concat . concat) . sample' $ arbitrary @[[[Integer]]]
    False
    >>> fmap (any ((> 30) . abs) . concat . concat . concat) . sample' $ arbitrary @[[[Int]]]
    False

We want to at least occasionally generate some larger ones, which is what the 'Arbitrary'
instance for 'Int64' does:

    >>> import Data.Int
    >>> fmap (any ((> 10000) . abs) . concat . concat . concat) . sample' $ arbitrary @[[[Int64]]]
    True

For this reason we use 'Int64' when dealing with QuickCheck.
-}

instance ArbitraryBuiltin Integer where
    arbitraryBuiltin = frequency
        [ (4, arbitrary @Integer)
        -- See Note [QuickCheck and integral types].
        , (1, fromIntegral <$> arbitrary @Int64)
        ]

-- |
--
-- >>> shrinkBuiltin $ Text.pack "abcd"
-- ["","cd","ab","bcd","acd","abd","abc","aacd","abad","abbd","abca","abcb","abcc"]
instance ArbitraryBuiltin Text where
    arbitraryBuiltin = Text.pack . getPrintableString <$> arbitrary
    shrinkBuiltin = map (Text.pack . getPrintableString) . shrink . PrintableString . Text.unpack

instance ArbitraryBuiltin ByteString where
    arbitraryBuiltin = Text.encodeUtf8 <$> arbitraryBuiltin
    shrinkBuiltin = map Text.encodeUtf8 . shrinkBuiltin . Text.decodeUtf8

instance ArbitraryBuiltin BLS12_381.G1.Element where
    arbitraryBuiltin = BLS12_381.G1.hashToGroup <$> arbitrary
    shrinkBuiltin _ = []

instance ArbitraryBuiltin BLS12_381.G2.Element where
    arbitraryBuiltin = BLS12_381.G2.hashToGroup <$> arbitrary
    shrinkBuiltin _ = []

instance ArbitraryBuiltin BLS12_381.Pairing.MlResult where
    arbitraryBuiltin = BLS12_381.Pairing.millerLoop <$> arbitraryBuiltin <*> arbitraryBuiltin
    shrinkBuiltin _ = []

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

instance Eq (MaybeSomeTypeOf k) where
    NothingSomeType   == NothingSomeType   = True
    JustSomeType uni1 == JustSomeType uni2 = uni1 `defaultEq` uni2
    NothingSomeType   == JustSomeType{}    = False
    JustSomeType{}    == NothingSomeType   = False

-- | Forget the reflected at the type level kind.
eraseMaybeSomeTypeOf :: MaybeSomeTypeOf k -> Maybe (SomeTypeIn DefaultUni)
eraseMaybeSomeTypeOf NothingSomeType    = Nothing
eraseMaybeSomeTypeOf (JustSomeType uni) = Just $ SomeTypeIn uni

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
shrinkToStarArgs :: DefaultUni (Esc a) -> [MaybeSomeTypeOf GHC.Type]
shrinkToStarArgs = go [] where
    go :: [MaybeSomeTypeOf GHC.Type] -> DefaultUni (Esc b) -> [MaybeSomeTypeOf GHC.Type]
    go args (fun `DefaultUniApply` arg) =
        go ([JustSomeType arg | SingType <- [toSingKind arg]] ++ args) fun
    go args _ = args

-- | Shrink a built-in type while preserving its kind.
shrinkDropBuiltinSameKind :: DefaultUni (Esc (a :: k)) -> [MaybeSomeTypeOf k]
shrinkDropBuiltinSameKind uni =
    case toSingKind uni of
        SingType -> case uni of
            -- 'DefaultUniUnit' is the "minimal" built-in type, can't shrink it any further.
            DefaultUniUnit -> []
            -- Any other built-in type of kind @*@ shrinks to 'DefaultUniUnit' and if it happens to
            -- be a built-in type application, then also all suitable arguments of the
            -- application that are not 'DefaultUniUnit'.
            _              ->
                let ju = JustSomeType DefaultUniUnit
                in ju : filter (/= ju) (shrinkToStarArgs uni)
        -- Any built-in type of kind @* -> *@ can be shrunk to @[] :: * -> *@ as long as the
        -- built-in type is not @[]@ already.
        -- If we had higher-kinded built-in types, we'd need 'shrinkToStarToStarArgs' here like with
        -- 'shrinkToStarArgs' above, so the current approach would need some generalization. But we
        -- we don't have higher-kinded built-in types and are unlikely to introduce them, so we opt
        -- for not complicating things here.
        SingType `SingKindArrow` SingType -> case uni of
            DefaultUniProtoList -> []
            _                   -> [JustSomeType DefaultUniProtoList]
        _ -> []

-- | Shrink a function application by shrinking either the function or the argument.
-- The kind is preserved.
shrinkDefaultUniApply :: DefaultUni (Esc (a :: k)) -> [MaybeSomeTypeOf k]
shrinkDefaultUniApply (fun `DefaultUniApply` arg) = concat
    [ [ JustSomeType $ fun' `DefaultUniApply` arg
      | JustSomeType fun' <- shrinkBuiltinSameKind fun
      ]
    , [ JustSomeType $ fun `DefaultUniApply` arg'
      | JustSomeType arg' <- shrinkBuiltinSameKind arg
      ]
    ]
shrinkDefaultUniApply _ = []

-- | Kind-preserving shrinking for 'DefaultUni'.
shrinkBuiltinSameKind :: DefaultUni (Esc (a :: k)) -> [MaybeSomeTypeOf k]
shrinkBuiltinSameKind uni = shrinkDropBuiltinSameKind uni ++ shrinkDefaultUniApply uni

{- Note [Kind-driven generation of built-in types]
The @Arbitrary (MaybeSomeTypeOf k)@ instance is responsible for generating built-in types.

We reflect the kind at the type-level, so that

1. generation of built-in types can be kind-driven
2. and we don't need to do any kind checking at runtime (or 'unsafeCoerce'-ing) in order to
   things into our intrisically kinded representation of built-in types

I.e. we have a correct-by-construction built-in type generator.
-}

-- See Note [Kind-driven generation of built-in types].
instance KnownKind k => Arbitrary (MaybeSomeTypeOf k) where
   arbitrary = do
       size <- getSize
       oneof $ case knownKind @k of
           SingType ->
               [genDefaultUniApply | size > 10] ++ map pure
               [ JustSomeType DefaultUniInteger
               , JustSomeType DefaultUniByteString
               , JustSomeType DefaultUniString
               , JustSomeType DefaultUniUnit
               , JustSomeType DefaultUniBool
               , JustSomeType DefaultUniData
               ]
           SingType `SingKindArrow` SingType ->
               [genDefaultUniApply | size > 10] ++
               [pure $ JustSomeType DefaultUniProtoList]
           SingType `SingKindArrow` SingType `SingKindArrow` SingType ->
               -- No 'genDefaultUniApply', because we don't have any built-in type constructors
               -- taking three or more arguments.
               [pure $ JustSomeType DefaultUniProtoPair]
           _ -> [pure NothingSomeType]

   shrink NothingSomeType    = []  -- No shrinks if you don't have anything to shrink.
   shrink (JustSomeType uni) = shrinkBuiltinSameKind uni

instance Arbitrary (Some (ValueOf DefaultUni)) where
    arbitrary = do
        mayUni <- arbitrary
        case mayUni of
            NothingSomeType  -> error "Panic: no *-kinded built-in types exist"
            JustSomeType uni ->
                bring (Proxy @ArbitraryBuiltin) uni $
                    Some . ValueOf uni <$> arbitraryBuiltin

    shrink (Some (ValueOf DefaultUniUnit ())) = []
    shrink (Some (ValueOf uni x))             = someValue () :
        bring (Proxy @ArbitraryBuiltin) uni (map (Some . ValueOf uni) $ shrinkBuiltin x)

-- | Generate a built-in type of a given kind.
genBuiltinTypeOf :: Kind () -> Gen (Maybe (SomeTypeIn DefaultUni))
genBuiltinTypeOf kind =
    -- See Note [Kind-driven generation of built-in types].
    withKnownKind kind $ \(_ :: Proxy kind) ->
        eraseMaybeSomeTypeOf <$> arbitrary @(MaybeSomeTypeOf kind)

-- | Shrink a built-in type by dropping a part of it or dropping the whole built-in type in favor of
-- a some minimal one (see 'shrinkDropBuiltinSameKind'). The kind is not preserved in the general
-- case.
shrinkDropBuiltin :: DefaultUni (Esc (a :: k)) -> [SomeTypeIn DefaultUni]
shrinkDropBuiltin uni = concat
    [ case toSingKind uni of
          SingType `SingKindArrow` _ -> shrinkDropBuiltin $ uni `DefaultUniApply` DefaultUniUnit
          _                          -> []
    , mapMaybe eraseMaybeSomeTypeOf $ shrinkDropBuiltinSameKind uni
    ]

-- TODO: have proper tests
-- >>> :set -XTypeApplications
-- >>> import PlutusCore.Pretty
-- >>> mapM_ (putStrLn . display) . shrinkBuiltinType $ someType @_ @[Bool]
-- unit
-- bool
-- (list unit)
-- >>> mapM_ (putStrLn . display) . shrinkBuiltinType $ someType @_ @(,)
-- unit
-- list
-- >>> mapM_ (putStrLn . display) . shrinkBuiltinType $ someType @_ @((,) Integer)
-- unit
-- integer
-- list
-- (pair unit)
-- >>> mapM_ (putStrLn . display) . shrinkBuiltinType $ someType @_ @((), Integer)
-- unit
-- integer
-- (list integer)
-- (pair unit unit)
-- >>> mapM_ (putStrLn . display) . shrinkBuiltinType $ someType @_ @([Bool], Integer)
-- unit
-- (list bool)
-- integer
-- (list integer)
-- (pair unit integer)
-- (pair bool integer)
-- (pair (list unit) integer)
-- (pair (list bool) unit)
-- | Non-kind-preserving shrinking for 'DefaultUni'.
shrinkBuiltinType :: SomeTypeIn DefaultUni -> [SomeTypeIn DefaultUni]
shrinkBuiltinType (SomeTypeIn uni) = concat
    [ shrinkDropBuiltin uni
    , mapMaybe eraseMaybeSomeTypeOf $ shrinkDefaultUniApply uni
    ]
