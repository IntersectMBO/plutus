-- | This module defines the 'TypedBuiltinGen' type and functions of this type.

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
    , genLowerBytes
    , genTypedBuiltinFail
    , genTypedBuiltinDef
    , genTypedBuiltinDivide
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Generators.Internal.Dependent

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe

import qualified Data.ByteString.Lazy                              as BSL
import           Data.Functor.Identity
import           Hedgehog                                          hiding (Size, Var)
import qualified Hedgehog.Gen                                      as Gen
import qualified Hedgehog.Range                                    as Range

-- | Generate a UTF-8 lazy 'ByteString' containg lower-case letters.
genLowerBytes :: Monad m => Range Int -> GenT m BSL.ByteString
genLowerBytes range = BSL.fromStrict <$> Gen.utf8 range Gen.lower

-- TODO: rename me to @TermWith@.
-- | A PLC 'Term' along with the correspoding Haskell value.
data TermOf uni a = TermOf
    { _termOfTerm  :: Term TyName Name uni ()  -- ^ The PLC term
    , _termOfValue :: a                        -- ^ The Haskell value.
    } deriving (Functor, Foldable, Traversable)
-- This has an interesting @Apply@ instance (no pun intended).

-- | A function of this type generates values of built-in typed (see 'TypedBuiltin' for
-- the list of such types) and returns it along with the corresponding PLC value.
type TypedBuiltinGenT uni m = forall a. AsKnownType uni a -> GenT m (TermOf uni a)

-- | 'TypedBuiltinGenT' specified to 'Identity'.
type TypedBuiltinGen uni = TypedBuiltinGenT uni Identity

instance (PrettyBy config a, PrettyBy config (Term TyName Name uni ())) =>
        PrettyBy config (TermOf uni a) where
    prettyBy config (TermOf t x) = prettyBy config t <+> "~>" <+> prettyBy config x

attachCoercedTerm
    :: (Monad m, KnownType uni a) => GenT m a -> GenT m (TermOf uni a)
attachCoercedTerm = fmap $ \x -> TermOf (makeKnown x) x

-- | Update a typed built-ins generator by overwriting the generator for a certain built-in.
updateTypedBuiltinGen
    :: forall a uni m. (GShow uni, KnownType uni a, Monad m)
    => GenT m a                 -- ^ A new generator.
    -> TypedBuiltinGenT uni m   -- ^ An old typed built-ins generator.
    -> TypedBuiltinGenT uni m   -- ^ The updated typed built-ins generator.
updateTypedBuiltinGen genX genTb akt@AsKnownType
    | Just Refl <- proxyAsKnownType genX `geq` akt = attachCoercedTerm genX
    | otherwise                                    = genTb akt

-- | A built-ins generator that always fails.
genTypedBuiltinFail :: (GShow uni, Monad m) => TypedBuiltinGenT uni m
genTypedBuiltinFail tb = fail $ fold
    [ "A generator for the following built-in is not implemented: "
    , prettyString tb
    ]

-- | A default built-ins generator.
genTypedBuiltinDef
    :: (GShow uni, GEq uni, uni `Includes` Integer, uni `Includes` BSL.ByteString, Monad m)
    => TypedBuiltinGenT uni m
genTypedBuiltinDef
    = updateTypedBuiltinGen @Integer
         (Gen.integral $ Range.linearFrom 0 0 10)
    $ updateTypedBuiltinGen
          (genLowerBytes (Range.linear 0 10))
    $ updateTypedBuiltinGen Gen.bool
    $ genTypedBuiltinFail

-- | A built-ins generator that doesn't produce @0 :: Integer@,
-- so that one case use 'div' or 'mod' over such integers without the risk of dividing by zero.
genTypedBuiltinDivide
    :: (GShow uni, GEq uni, uni `Includes` Integer, uni `Includes` BSL.ByteString, Monad m)
    => TypedBuiltinGenT uni m
genTypedBuiltinDivide
    = updateTypedBuiltinGen @Integer
          (Gen.filter (/= 0) . Gen.integral $ Range.linear 0 10)
    $ genTypedBuiltinDef
