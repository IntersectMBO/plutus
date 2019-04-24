-- | This module defines the 'TypedBuiltinGen' type and functions of this type
-- which control size-induced bounds of values generated.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Generators.Internal.TypedBuiltinGen
    ( TermOf(..)
    , TypedBuiltinGenT
    , TypedBuiltinGen
    , genLowerBytes
    , updateTypedBuiltinGenInt
    , updateTypedBuiltinGenBS
    , updateTypedBuiltinGenBool
    , genTypedBuiltinFail
    , genTypedBuiltinDef
    , genTypedBuiltinDivide
    ) where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Language.PlutusCore.Generators.Internal.Dependent ()

import qualified Data.ByteString.Lazy                              as BSL
import           Data.Functor.Identity
import           Data.GADT.Compare
import           Hedgehog                                          hiding (Size, Var)
import qualified Hedgehog.Gen                                      as Gen
import qualified Hedgehog.Range                                    as Range

-- | Generate a UTF-8 lazy 'ByteString' containg lower-case letters.
genLowerBytes :: Monad m => Range Int -> GenT m BSL.ByteString
genLowerBytes range = BSL.fromStrict <$> Gen.utf8 range Gen.lower

-- TODO: rename me to @TermWith@.
-- | A PLC 'Term' along with the correspoding Haskell value.
data TermOf a = TermOf
    { _termOfTerm  :: Term TyName Name ()  -- ^ The PLC term
    , _termOfValue :: a                    -- ^ The Haskell value.
    } deriving (Functor, Foldable, Traversable)
-- This has an interesting @Apply@ instance (no pun intended).

-- | A function of this type generates values of built-in typed (see 'TypedBuiltin' for
-- the list of such types) and returns it along with the corresponding PLC value.
-- Bounds induced (as per the spec) by the 'Size' values must be met, but can be narrowed.
type TypedBuiltinGenT m = forall a. TypedBuiltin a -> GenT m (TermOf a)

-- | 'TypedBuiltinGenT' specified to 'Identity'.
type TypedBuiltinGen = TypedBuiltinGenT Identity

instance (PrettyBy config a, PrettyBy config (Term TyName Name ())) =>
        PrettyBy config (TermOf a) where
    prettyBy config (TermOf t x) = prettyBy config t <+> "~>" <+> prettyBy config x

attachCoercedTerm
    :: Monad m => PrettyDynamic a => TypedBuiltin a -> GenT m a -> GenT m (TermOf a)
attachCoercedTerm tb genX = do
    x <- genX
    -- Previously we used 'unsafeMakeBuiltin' here, however it didn't allow to generate
    -- terms with out-of-bounds constants. Hence we now use 'makeBuiltinNOCHECK'.
    -- The right thing would be to parameterize this function by a built-in maker,
    -- so we check bounds when this makes sense and do not check otherwise.
    -- But this function is used rather deeply in the pipeline, so we need to
    -- attach a 'ReaderT' to 'm' instead of parameterizing the function and
    -- this just makes everything convoluted. We anyway check bounds down the pipeline.
    let term = makeBuiltinNOCHECK $ TypedBuiltinValue tb x
    return $ TermOf term x

-- | Update a typed built-ins generator by overwriting the generator for a certain built-in.
updateTypedBuiltinGen
    :: (Monad m, PrettyDynamic a)
    => TypedBuiltin a       -- ^ A generator of which built-in to overwrite.
    -> GenT m a             -- ^ A new generator.
    -> TypedBuiltinGenT m   -- ^ An old typed built-ins generator.
    -> TypedBuiltinGenT m   -- ^ The updated typed built-ins generator.
updateTypedBuiltinGen tbNew genX genTb tbOld
    | Just Refl <- tbNew `geq` tbOld = attachCoercedTerm tbOld genX
    | otherwise                      = genTb tbOld

-- | Update a typed built-ins generator by overwriting the generator for a certain built-in.
updateTypedBuiltinGenStatic
    :: (Monad m, PrettyDynamic a)
    => TypedBuiltinStatic a  -- ^ A generator of which sized built-in to overwrite.
    -> GenT m a             -- ^ A new generator
    -> TypedBuiltinGenT m   -- ^ An old typed built-ins generator.
    -> TypedBuiltinGenT m   -- ^ The updated typed built-ins generator.
updateTypedBuiltinGenStatic tbsNew genX genTb tbOld = case tbOld of
    TypedBuiltinStatic tbsOld | Just Refl <- tbsNew `geq` tbsOld -> attachCoercedTerm tbOld genX
    _                                                           -> genTb tbOld

-- | Update a typed built-ins generator by overwriting the @integer@s generator.
updateTypedBuiltinGenInt
    :: Monad m
    => GenT m Integer -> TypedBuiltinGenT m -> TypedBuiltinGenT m
updateTypedBuiltinGenInt = updateTypedBuiltinGenStatic TypedBuiltinStaticInt

-- | Update a typed built-ins generator by overwriting the @bytestring@s generator.
updateTypedBuiltinGenBS
    :: Monad m
    => GenT m BSL.ByteString -> TypedBuiltinGenT m -> TypedBuiltinGenT m
updateTypedBuiltinGenBS = updateTypedBuiltinGenStatic TypedBuiltinStaticBS

-- | Update a typed built-ins generator by overwriting the @boolean@s generator.
updateTypedBuiltinGenBool
    :: Monad m
    => GenT m Bool -> TypedBuiltinGenT m -> TypedBuiltinGenT m
updateTypedBuiltinGenBool = updateTypedBuiltinGen $ TypedBuiltinDyn @Bool

-- | A built-ins generator that always fails.
genTypedBuiltinFail :: Monad m => TypedBuiltinGenT m
genTypedBuiltinFail tb = fail $ fold
    [ "A generator for the following built-in is not implemented: "
    , prettyString tb
    ]

-- | A default built-ins generator that produces values in bounds seen in the spec.
genTypedBuiltinDef :: Monad m => TypedBuiltinGenT m
genTypedBuiltinDef
    = updateTypedBuiltinGenInt
         (Gen.integral $ Range.linearFrom 0 0 10)
    $ updateTypedBuiltinGenBS
          (genLowerBytes $ Range.linear 0 10)
    $ updateTypedBuiltinGenBool Gen.bool
    $ genTypedBuiltinFail

-- so that one case use 'div' or 'mod' over such integers without the risk of dividing by zero.
genTypedBuiltinDivide :: Monad m => TypedBuiltinGenT m
genTypedBuiltinDivide
    = updateTypedBuiltinGenInt
          (Gen.filter (/= 0) . Gen.integral $ Range.linear 0 10)
    $ genTypedBuiltinDef
