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

module PlutusCore.Generators.Internal.TypedBuiltinGen
    ( TermOf(..)
    , TypedBuiltinGenT
    , TypedBuiltinGen
    , Generatable
    , genLowerBytes
    , genTypedBuiltinFail
    , genTypedBuiltinDef
    ) where

import           PlutusPrelude

import           PlutusCore.Generators.Internal.Dependent

import           PlutusCore.Constant
import           PlutusCore.Core
import           PlutusCore.Default.Universe
import           PlutusCore.Evaluation.Result
import           PlutusCore.Pretty.PrettyConst

import qualified Data.ByteString                          as BS
import           Data.Functor.Identity
import           Data.Text.Prettyprint.Doc
import           Hedgehog                                 hiding (Size, Var)
import qualified Hedgehog.Gen                             as Gen
import qualified Hedgehog.Range                           as Range

-- | Generate a UTF-8 lazy 'ByteString' containg lower-case letters.
genLowerBytes :: Monad m => Range Int -> GenT m BS.ByteString
genLowerBytes range = Gen.utf8 range Gen.lower

-- TODO: rename me to @TermWith@.
-- | A @term@ along with the correspoding Haskell value.
data TermOf term a = TermOf
    { _termOfTerm  :: term  -- ^ The term
    , _termOfValue :: a     -- ^ The Haskell value.
    } deriving (Functor, Foldable, Traversable)

-- | A function of this type generates values of built-in typed (see 'TypedBuiltin' for
-- the list of such types) and returns it along with the corresponding PLC value.
type TypedBuiltinGenT term m = forall a. AsKnownType term a -> GenT m (TermOf term a)

-- | 'TypedBuiltinGenT' specified to 'Identity'.
type TypedBuiltinGen term = TypedBuiltinGenT term Identity

type Generatable uni = (GShow uni, GEq uni, DefaultUni <: uni)

instance (PrettyBy config a, PrettyBy config term) =>
        PrettyBy config (TermOf term a) where
    prettyBy config (TermOf t x) = prettyBy config t <+> "~>" <+> prettyBy config x

attachCoercedTerm
    :: (Monad m, KnownType term a, PrettyConst a)
    => GenT m a -> GenT m (TermOf term a)
attachCoercedTerm a = do
    x <- a
    case makeKnownNoEmit x of
        -- I've attempted to implement support for generating 'EvaluationFailure',
        -- but it turned out to be too much of a pain for something that we do not really need.
        EvaluationFailure -> fail $ concat
            [ "Got 'EvaluationFailure' when generating a value of a built-in type: "
            , show $ prettyConst x
            ]
        EvaluationSuccess v -> pure $ TermOf v x

-- | Update a typed built-ins generator by overwriting the generator for a certain built-in.
updateTypedBuiltinGen
    :: forall a term m. (GShow (UniOf term), KnownType term a, PrettyConst a, Monad m)
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
genTypedBuiltinDef
    :: (Generatable uni, HasConstantIn uni term, Monad m)
    => TypedBuiltinGenT term m
genTypedBuiltinDef
    = updateTypedBuiltinGen @Integer (Gen.integral $ Range.linearFrom 0 0 10)
    $ updateTypedBuiltinGen (genLowerBytes (Range.linear 0 10))
    $ updateTypedBuiltinGen Gen.bool
    $ genTypedBuiltinFail
