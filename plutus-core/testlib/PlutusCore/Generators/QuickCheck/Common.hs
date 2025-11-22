{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusCore.Generators.QuickCheck.Common where

import PlutusPrelude

import PlutusCore.Default
import PlutusCore.Name.Unique
import PlutusCore.TypeCheck (defKindCheckConfig)
import PlutusCore.TypeCheck.Internal (inferKindM, runTypeCheckM, withTyVar)
import PlutusIR
import PlutusIR.Error

import Control.Monad.Except
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Stack
import Test.QuickCheck.Gen (Gen)
import Test.QuickCheck.Gen qualified as Gen
import Test.QuickCheck.Modifiers (NonNegative (..))
import Test.QuickCheck.Property
import Text.PrettyBy.Internal

instance Testable (Either String ()) where
  property =
    property . \case
      Left err -> failed {reason = err}
      Right () -> succeeded

deriving newtype instance Pretty i => Pretty (NonNegative i)
instance PrettyBy config i => DefaultPrettyBy config (NonNegative i)
deriving via
  PrettyCommon (NonNegative i)
  instance
    PrettyDefaultBy config (NonNegative i) => PrettyBy config (NonNegative i)

type TypeCtx = Map TyName (Kind ())

-- | Infer the kind of a type in a given kind context
inferKind :: TypeCtx -> Type TyName DefaultUni () -> Either String (Kind ())
inferKind ctx ty =
  first display . modifyError (PLCTypeError) . runTypeCheckM defKindCheckConfig $
    foldr
      (uncurry withTyVar)
      (inferKindM @_ @DefaultUni @DefaultFun ty)
      (Map.toList ctx)

{-| Partial unsafeInferKind, useful for context where invariants are set up to guarantee
that types are well-kinded. -}
unsafeInferKind :: HasCallStack => TypeCtx -> Type TyName DefaultUni () -> Kind ()
unsafeInferKind ctx ty =
  case inferKind ctx ty of
    Left msg -> error msg
    Right k -> k

-- | Check well-kindedness of a type in a context
checkKind :: TypeCtx -> Type TyName DefaultUni () -> Kind () -> Either String ()
checkKind ctx ty kExp =
  if kInf == Right kExp
    then Right ()
    else
      Left $
        concat
          [ "Inferred kind is "
          , display kInf
          , " while expected "
          , display kExp
          ]
  where
    kInf = inferKind ctx ty

{-| Generate a list with the given minimum and maximum lengths.
It is similar to @Hedgehog.Internal.Gen.list@.

Note that @genList 0 n gen@ behaves differently than @resize n (listOf gen)@, because

@
   resize m (genList 0 n gen) = genList 0 n (resize m gen)
@

whereas

@
   resize m (resize n (listOf gen)) = resize n (listOf gen)
@ -}
genList :: Int -> Int -> Gen a -> Gen [a]
genList lb ub gen = do
  len <- Gen.chooseInt (lb, ub)
  Gen.vectorOf len gen
