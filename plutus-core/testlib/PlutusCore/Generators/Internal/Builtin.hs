{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE TypeApplications    #-}

module PlutusCore.Generators.Internal.Builtin (
    genConstant,
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

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Data (Data (..))
import PlutusCore.Generators.AST (genTerm, runAstGen)

import Data.ByteString qualified as BS
import Data.Int (Int64)
import Data.Text (Text)
import Data.Type.Equality
import Data.Typeable (splitTyConApp)
import Hedgehog hiding (Opaque, Var, eval)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Type.Reflection

genConstant :: forall a. TypeRep a -> Gen a
genConstant tr
    | Just HRefl <- eqTypeRep tr (typeRep @()) = pure ()
    | Just HRefl <- eqTypeRep tr (typeRep @Integer) = genInteger
    | Just HRefl <- eqTypeRep tr (typeRep @Int) = fromIntegral <$> genInteger
    | Just HRefl <- eqTypeRep tr (typeRep @Bool) = Gen.bool
    | Just HRefl <- eqTypeRep tr (typeRep @BS.ByteString) = genByteString
    | Just HRefl <- eqTypeRep tr (typeRep @Text) = genText
    | Just HRefl <- eqTypeRep tr (typeRep @Data) = genData 5
    | Just HRefl <- eqTypeRep tr (typeRep @(Term TyName Name DefaultUni DefaultFun ())) =
        runAstGen genTerm
    | trPair `App` tr1 `App` tr2 <- tr
    , Just HRefl <- eqTypeRep trPair (typeRep @(,)) =
        (,) <$> genConstant tr1 <*> genConstant tr2
    | trList `App` trElem <- tr
    , Just HRefl <- eqTypeRep trList (typeRep @[]) =
        Gen.list (Range.linear 0 10) $ genConstant trElem
    | trOpaque `App` trVal `App` _ <- tr
    , Just HRefl <- eqTypeRep trOpaque (typeRep @Opaque) =
        Opaque <$> genConstant trVal
    | trSomeConstant `App` trUni `App` _ <- tr
    , Just HRefl <- eqTypeRep trUni (typeRep @DefaultUni)
    , Just HRefl <- eqTypeRep trSomeConstant (typeRep @SomeConstant) =
        -- In the current implementation, all type variables are instantiated
        -- to `Integer` (TODO: change this).
        SomeConstant . someValue <$> genInteger
    | otherwise =
        error $
            "genConstant: I don't know how to generate constant of this type: " <> show tr

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
