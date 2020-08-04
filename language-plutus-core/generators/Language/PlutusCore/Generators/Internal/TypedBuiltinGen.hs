-- | This module defines the 'TypedBuiltinGen' type and functions of this type.

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Generators.Internal.TypedBuiltinGen
    ( TermOf(..)
    , TypedBuiltinGenT
    , TypedBuiltinGen
    , Generatable
    , genLowerBytes
    , genTypedBuiltinFail
    , genTypedBuiltinDef
    , genTypedBuiltinDivide
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Generators.Internal.Dependent

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Universe

import qualified Data.ByteString.Lazy                              as BSL
import           Data.Functor.Identity
import           Data.Text.Prettyprint.Doc
import           Hedgehog                                          hiding (Size, Var)
import qualified Hedgehog.Gen                                      as Gen
import qualified Hedgehog.Internal.Gen                             as Gen
import qualified Hedgehog.Range                                    as Range

-- | Generate a UTF-8 lazy 'ByteString' containg lower-case letters.
genLowerBytes :: Monad m => Range Int -> GenT m BSL.ByteString
genLowerBytes range = BSL.fromStrict <$> Gen.utf8 range Gen.lower

-- TODO: rename me to @TermWith@.
-- | A @term@ along with the correspoding Haskell value.
data TermOf term a = TermOf
    { _termOfTerm  :: EvaluationResult term  -- ^ The term
    , _termOfValue :: a                      -- ^ The Haskell value.
    } deriving (Functor, Foldable, Traversable)

-- | A function of this type generates values of built-in typed (see 'TypedBuiltin' for
-- the list of such types) and returns it along with the corresponding PLC value.
type TypedBuiltinGenT term m = forall a. AsKnownType term a -> GenT m (TermOf term a)

-- | 'TypedBuiltinGenT' specified to 'Identity'.
type TypedBuiltinGen term = TypedBuiltinGenT term Identity

type Generatable term =
    ( GShow (UniOf term)
    , GEq (UniOf term)
    , DefaultUni <: UniOf term
    , HasConstant term
    )

instance (PrettyBy config a, PrettyBy config term) =>
        PrettyBy config (TermOf term a) where
    prettyBy config (TermOf t x) = prettyBy config t <+> "~>" <+> prettyBy config x

attachCoercedTerm
    :: (Monad m, KnownType term a) => GenT m a -> GenT m (TermOf term a)
attachCoercedTerm = fmap $ \x -> TermOf (makeKnown x) x

-- | Update a typed built-ins generator by overwriting the generator for a certain built-in.
updateTypedBuiltinGen
    :: forall a term m. (GShow (UniOf term), KnownType term a, Monad m)
    => GenT m a                  -- ^ A new generator.
    -> TypedBuiltinGenT term m   -- ^ An old typed built-ins generator.
    -> TypedBuiltinGenT term m   -- ^ The updated typed built-ins generator.
updateTypedBuiltinGen genX genTb akt@AsKnownType
    | Just Refl <- proxyAsKnownType genX `geq` akt = attachCoercedTerm genX
    | otherwise                                    = genTb akt

-- | A built-ins generator that always fails.
genTypedBuiltinFail :: (GShow (UniOf term), Monad m) => TypedBuiltinGenT term m
genTypedBuiltinFail tb = fail $ fold
    [ "A generator for the following built-in is not implemented: "
    , display tb
    ]

-- | A default built-ins generator.
genTypedBuiltinDef :: (Generatable term, Monad m) => TypedBuiltinGenT term m
genTypedBuiltinDef
    = updateTypedBuiltinGen @Integer (Gen.integral $ Range.linearFrom 0 0 10)
    $ updateTypedBuiltinGen (genLowerBytes (Range.linear 0 10))
    $ updateTypedBuiltinGen Gen.bool
    $ genTypedBuiltinFail

-- | A built-ins generator that doesn't produce @0 :: Integer@,
-- so that one case use 'div' or 'mod' over such integers without the risk of dividing by zero.
genTypedBuiltinDivide :: (Generatable term, Monad m) => TypedBuiltinGenT term m
genTypedBuiltinDivide
    = updateTypedBuiltinGen @Integer
          (fromGenT (Gen.filterT (/= 0) . Gen.integral $ Range.linear 0 10))
    $ genTypedBuiltinDef
