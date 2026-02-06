{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module PlutusCore.Generators.Hedgehog.Builtin
  ( GenTypedTerm (..)
  , GenArbitraryTerm (..)
  , genConstant
  ) where

import PlutusCore hiding (Constr)
import PlutusCore.Builtin
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data (Data (..))
import PlutusCore.Evaluation.Machine.ExMemoryUsage
  ( DataNodeCount
  , IntegerCostedLiterally
  , NumBytesCostedAsNumWords
  , ValueMaxDepth
  , ValueTotalSize
  )
import PlutusCore.Generators.Hedgehog.AST hiding
  ( genConstant
  )
import PlutusCore.Generators.QuickCheck.Builtin
import PlutusCore.Value (Value)

import Data.ByteString qualified as BS
import Data.Int (Int64)
import Data.Kind qualified as GHC
import Data.Text (Text)
import Data.Type.Equality
import Data.Vector.Strict (Vector)
import Data.Vector.Strict qualified as Vector
import Data.Word (Word8)
import GHC.Natural
import Hedgehog hiding
  ( Opaque
  , Var
  , eval
  )
import Hedgehog.Gen qualified as Gen
import Hedgehog.Gen.QuickCheck (arbitrary)
import Hedgehog.Range qualified as Range
import Type.Reflection

{-| This class exists so we can provide an ad-hoc typed term generator
for various universes. We usually rely-on a universe-specific generator
for well-typed constants within that universe.

TODO: Move this to "PlutusIR.Generators.AST", and merge `genConstant` with
`PlutusIR.Generators.AST.genConstant`. -}
class GenTypedTerm uni where
  -- | Generate a `Term` in @uni@ with the given type.
  genTypedTerm
    :: forall (a :: GHC.Type) fun
     . KnownTypeAst TyName uni a
    => TypeRep a
    -> Gen (Term TyName Name uni fun ())

instance GenTypedTerm DefaultUni where
  -- TODO: currently it generates constants or constant functions returning constants.
  genTypedTerm tr0 = go (toTypeAst tr0) tr0
    where
      go
        :: forall (a :: GHC.Type) fun
         . Type TyName DefaultUni ()
        -> TypeRep a
        -> Gen (Term TyName Name DefaultUni fun ())
      go sch tr
        | trOpaque `App` _ `App` trEl <- tr
        , Just HRefl <- eqTypeRep trOpaque (typeRep @Opaque) =
            go sch trEl
      go (TyFun _ dom cod) tr
        | trFun `App` _ `App` trCod <- tr
        , Just HRefl <- eqTypeRep trFun (typeRep @(->)) =
            LamAbs () (Name "_" (Unique 0)) dom <$> go cod trCod
      go _ tr = case genConstant tr of
        SomeGen gen -> Constant () . someValue <$> gen

{-| This class exists so we can provide an ad-hoc arbitrary term generator
for various universes. -}
class GenArbitraryTerm uni where
  -- | Generate an arbitrary `Term` in @uni@.
  genArbitraryTerm
    :: forall fun
     . (Bounded fun, Enum fun)
    => Gen (Term TyName Name uni fun ())

instance GenArbitraryTerm DefaultUni where
  genArbitraryTerm = runAstGen genTerm

data SomeGen uni = forall a. uni `HasTermLevel` a => SomeGen (Gen a)

genArbitraryBuiltin
  :: forall a. (ArbitraryBuiltin a, DefaultUni `HasTermLevel` a) => SomeGen DefaultUni
genArbitraryBuiltin = SomeGen $ unAsArbitraryBuiltin <$> arbitrary @(AsArbitraryBuiltin a)

genConstant :: forall (a :: GHC.Type). TypeRep a -> SomeGen DefaultUni
genConstant tr
  | Just HRefl <- eqTypeRep tr (typeRep @()) = genArbitraryBuiltin @()
  | Just HRefl <- eqTypeRep tr (typeRep @Integer) = genArbitraryBuiltin @Integer
  | Just HRefl <- eqTypeRep tr (typeRep @Int) = genArbitraryBuiltin @Integer
  | Just HRefl <- eqTypeRep tr (typeRep @Int64) = genArbitraryBuiltin @Integer
  | Just HRefl <- eqTypeRep tr (typeRep @Word8) = genArbitraryBuiltin @Integer
  | Just HRefl <- eqTypeRep tr (typeRep @Natural) = genArbitraryBuiltin @Integer
  | Just HRefl <- eqTypeRep tr (typeRep @NumBytesCostedAsNumWords) = genArbitraryBuiltin @Integer
  | Just HRefl <- eqTypeRep tr (typeRep @IntegerCostedLiterally) = genArbitraryBuiltin @Integer
  | Just HRefl <- eqTypeRep tr (typeRep @Bool) = genArbitraryBuiltin @Bool
  | Just HRefl <- eqTypeRep tr (typeRep @BS.ByteString) = genArbitraryBuiltin @BS.ByteString
  | Just HRefl <- eqTypeRep tr (typeRep @Text) = genArbitraryBuiltin @Text
  | Just HRefl <- eqTypeRep tr (typeRep @Data) = genArbitraryBuiltin @Data
  | Just HRefl <- eqTypeRep tr (typeRep @DataNodeCount) = genArbitraryBuiltin @Data
  | Just HRefl <- eqTypeRep tr (typeRep @BLS12_381.G1.Element) =
      genArbitraryBuiltin @BLS12_381.G1.Element
  | Just HRefl <- eqTypeRep tr (typeRep @BLS12_381.G2.Element) =
      genArbitraryBuiltin @BLS12_381.G2.Element
  | Just HRefl <- eqTypeRep tr (typeRep @BLS12_381.Pairing.MlResult) =
      genArbitraryBuiltin @BLS12_381.Pairing.MlResult
  | Just HRefl <- eqTypeRep tr (typeRep @Value) = genArbitraryBuiltin @Value
  | Just HRefl <- eqTypeRep tr (typeRep @ValueTotalSize) = genArbitraryBuiltin @Value
  | Just HRefl <- eqTypeRep tr (typeRep @ValueMaxDepth) = genArbitraryBuiltin @Value
  | trPair `App` tr1 `App` tr2 <- tr
  , Just HRefl <- eqTypeRep trPair (typeRep @(,)) =
      -- We can perhaps use the @QuickCheck@ generator here too, but this seems rather hard.
      -- Maybe we should simply copy the logic. Should we halve the size explicitly here?
      case (genConstant tr1, genConstant tr2) of
        (SomeGen g1, SomeGen g2) -> SomeGen $ (,) <$> g1 <*> g2
  | trList `App` trElem <- tr
  , Just HRefl <- eqTypeRep trList (typeRep @[]) =
      case genConstant trElem of
        SomeGen genElem -> SomeGen $ Gen.list (Range.linear 0 10) genElem
  | trArray `App` trElem <- tr
  , Just HRefl <- eqTypeRep trArray (typeRep @Vector) =
      case genConstant trElem of SomeGen genElem -> SomeGen (genArray genElem)
  | trSomeConstant `App` _ `App` trEl <- tr
  , Just HRefl <- eqTypeRep trSomeConstant (typeRep @SomeConstant) =
      genConstant trEl
  | trLastArg `App` _ `App` trY <- tr
  , Just HRefl <- eqTypeRep trLastArg (typeRep @LastArg) =
      genConstant trY
  | trTyVarRep `App` _ <- tr
  , Just HRefl <- eqTypeRep trTyVarRep (typeRep @(TyVarRep @GHC.Type)) =
      -- In the current implementation, all type variables are instantiated
      -- to `Integer` (TODO: change this?).
      genArbitraryBuiltin @Integer
  | otherwise =
      error $
        "genConstant: I don't know how to generate constants of this type: " <> show tr
  where
    genArray :: Gen x -> Gen (Vector x)
    genArray = fmap Vector.fromList . Gen.list (Range.linear 0 10)
