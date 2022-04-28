{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE TypeApplications    #-}

module PlutusCore.Generators.Internal.Builtin (
    genValArg,
    genInteger,
    genByteString,
    genText,
    genData,
    genI,
    genB,
    genList,
    genMap,
    genConstr,
    matchTyCon,
) where

import Data.ByteString qualified as BS
import Data.Int (Int64)
import Data.Kind qualified as GHC
import Data.Text (Text)
import Data.Type.Equality
import Data.Typeable (splitTyConApp)
import Hedgehog hiding (Opaque, Var, eval)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore hiding (Term)
import PlutusCore.Builtin
import PlutusCore.Data (Data (..))
import Type.Reflection
import Unsafe.Coerce

-- | Generate one value argument to a builtin function based on its `TypeRep`.
genValArg :: forall k (a :: k). TypeRep a -> Gen (Some (ValueOf DefaultUni))
genValArg tr
    | Just HRefl <- eqTypeRep tr (typeRep @()) = pure $ someValue ()
    | Just HRefl <- eqTypeRep tr (typeRep @Integer) = someValue <$> genInteger
    | Just HRefl <- eqTypeRep tr (typeRep @Int) = someValue <$> genInteger
    | Just HRefl <- eqTypeRep tr (typeRep @Bool) = someValue <$> Gen.bool
    | Just HRefl <- eqTypeRep tr (typeRep @BS.ByteString) = someValue <$> genByteString
    | Just HRefl <- eqTypeRep tr (typeRep @Text) = someValue <$> genText
    | Just HRefl <- eqTypeRep tr (typeRep @Data) = someValue <$> genData 5
    | Just [SomeTypeRep tr1, SomeTypeRep tr2] <- matchTyCon @(,) tr = do
        Some (ValueOf uni1 val1) <- genValArg tr1
        Some (ValueOf uni2 val2) <- genValArg tr2
        pure
            ( someValueOf
                (DefaultUniApply (DefaultUniApply DefaultUniProtoPair uni1) uni2)
                (val1, val2)
            )
    | Just [SomeTypeRep trElem] <- matchTyCon @[] tr = do
        Some (ValueOf uniElem (_ :: b)) <- genValArg trElem
        args <- Gen.list (Range.linear 0 10) $ genValArg trElem
        let valElems :: [b]
            valElems = (\(Some (ValueOf _ valElem')) -> unsafeCoerce valElem') <$> args
        pure (someValueOf (DefaultUniApply DefaultUniProtoList uniElem) valElems)
    -- Descend upon `Opaque`
    | Just [_, SomeTypeRep tr'] <- matchTyCon @Opaque tr = genValArg tr'
    -- Descend upon `SomeConstant`
    | Just [_, SomeTypeRep tr'] <- matchTyCon @SomeConstant tr = genValArg tr'
    -- In the current implementation, all type variables are instantiated
    -- to `Integer` (TODO: change this).
    | Just _ <- matchTyCon @(TyVarRep @GHC.Type) tr =
        someValue <$> genInteger
    | otherwise =
        error $
            "genValArg: I don't know how to generate builtin arguments of this type: " <> show tr

-- | If the given `TypeRep`'s `TyCon` is @con@, return its type arguments.
matchTyCon :: forall con a. (Typeable con) => TypeRep a -> Maybe [SomeTypeRep]
matchTyCon tr = if con == con' then Just args else Nothing
  where
    (con, args) = splitTyConApp (SomeTypeRep tr)
    con' = typeRepTyCon (typeRep @con)

----------------------------------------------------------
-- Generators

genInteger :: Gen Integer
genInteger = fromIntegral @Int64 <$> Gen.enumBounded

genByteString :: Gen BS.ByteString
genByteString = Gen.utf8 (Range.linear 0 100) Gen.enumBounded

genText :: Gen Text
genText = Gen.text (Range.linear 0 100) Gen.enumBounded

genData :: Int -> Gen Data
genData depth =
    Gen.choice $
        [genI, genB]
            <> [ genRec | depth > 1, genRec <-
                                        [ genList (depth - 1)
                                        , genMap (depth - 1)
                                        , genConstr (depth - 1)
                                        ]
               ]

genI :: Gen Data
genI = I <$> genInteger

genB :: Gen Data
genB = B <$> genByteString

genList :: Int -> Gen Data
genList depth = List <$> Gen.list (Range.linear 0 5) (genData (depth - 1))

genMap :: Int -> Gen Data
genMap depth =
    Map
        <$> Gen.list
            (Range.linear 0 5)
            ((,) <$> genData (depth - 1) <*> genData (depth - 1))

genConstr :: Int -> Gen Data
genConstr depth =
    Constr <$> genInteger
        <*> Gen.list
            (Range.linear 0 5)
            (genData (depth - 1))
