{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module defines the 'TypedBuiltinGen' type and functions of this type.
module PlutusCore.Generators.Hedgehog.TypedBuiltinGen
  ( TermOf (..)
  , TypedBuiltinGenT
  , TypedBuiltinGen
  , genLowerBytes
  , genTypedBuiltinFail
  , genTypedBuiltinDef
  ) where

import PlutusPrelude

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Pretty

import Data.ByteString qualified as BS
import Data.Functor.Identity
import Hedgehog hiding (Size, Var)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Prettyprinter
import Type.Reflection

-- | Generate a UTF-8 lazy 'ByteString' containing lower-case letters.
genLowerBytes :: Monad m => Range Int -> GenT m BS.ByteString
genLowerBytes range = Gen.utf8 range Gen.lower

-- TODO: rename me to @TermWith@.
-- | A @term@ along with the corresponding Haskell value.
data TermOf term a = TermOf
  { _termOfTerm :: term
  -- ^ The term
  , _termOfValue :: a
  -- ^ The Haskell value.
  }
  deriving stock (Functor, Foldable, Traversable)

{-| A function of this type generates values of built-in typed (see 'TypedBuiltin' for
the list of such types) and returns it along with the corresponding PLC value. -}
type TypedBuiltinGenT term m = forall a. TypeRep a -> GenT m (TermOf term a)

-- | 'TypedBuiltinGenT' specified to 'Identity'.
type TypedBuiltinGen term = TypedBuiltinGenT term Identity

instance
  (PrettyBy config a, PrettyBy config term)
  => PrettyBy config (TermOf term a)
  where
  prettyBy config (TermOf t x) = prettyBy config t <+> "~>" <+> prettyBy config x

attachCoercedTerm
  :: (Monad m, MakeKnown term a, PrettyConst a)
  => GenT m a -> GenT m (TermOf term a)
attachCoercedTerm a = do
  x <- a
  case makeKnownOrFail x of
    -- I've attempted to implement support for generating 'EvaluationFailure',
    -- but it turned out to be too much of a pain for something that we do not really need.
    EvaluationFailure ->
      fail $
        concat
          [ "Got 'EvaluationFailure' when generating a value of a built-in type: "
          , render $ prettyConst botRenderContext x
          ]
    EvaluationSuccess res -> pure $ TermOf res x

-- | Update a typed built-ins generator by overwriting the generator for a certain built-in.
updateTypedBuiltinGen
  :: forall a term m
   . (Typeable a, MakeKnown term a, PrettyConst a, Monad m)
  => GenT m a
  -- ^ A new generator.
  -> TypedBuiltinGenT term m
  -- ^ An old typed built-ins generator.
  -> TypedBuiltinGenT term m
  -- ^ The updated typed built-ins generator.
updateTypedBuiltinGen genX genTb tr
  | Just Refl <- typeRep @a `geq` tr = attachCoercedTerm genX
  | otherwise = genTb tr

-- | A built-ins generator that always fails.
genTypedBuiltinFail :: Monad m => TypedBuiltinGenT term m
genTypedBuiltinFail tb =
  fail $
    fold
      [ "A generator for the following built-in is not implemented: "
      , show tb
      ]

-- | A default built-ins generator.
genTypedBuiltinDef
  :: (HasConstantIn DefaultUni term, Monad m)
  => TypedBuiltinGenT term m
genTypedBuiltinDef =
  updateTypedBuiltinGen @Integer (Gen.integral $ Range.linearFrom 0 0 10) $
    updateTypedBuiltinGen (genLowerBytes (Range.linear 0 10)) $
      updateTypedBuiltinGen Gen.bool $
        genTypedBuiltinFail
