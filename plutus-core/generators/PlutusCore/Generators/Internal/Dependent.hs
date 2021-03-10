-- | Orphan 'GEq' and 'GCompare' instances of data types from "Language.PlutusCore.Constant.Typed".
-- The reason we keep the instances separate is that they are highly unsafe ('unsafeCoerce' is used)
-- and needed only for tests.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.PlutusCore.Generators.Internal.Dependent
    ( AsKnownType (..)
    , proxyAsKnownType
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Universe

import           Data.GADT.Compare
import           Unsafe.Coerce

liftOrdering :: Ordering -> GOrdering a b
liftOrdering LT = GLT
liftOrdering EQ = error "'liftOrdering': 'Eq'"
liftOrdering GT = GGT

-- | Contains a proof that @a@ is a 'KnownType'.
data AsKnownType term a where
    AsKnownType :: KnownType term a => AsKnownType term a

instance GShow (UniOf term) => Pretty (AsKnownType term a) where
    pretty a@AsKnownType = pretty $ toTypeAst @_ @(UniOf term) a

instance GShow (UniOf term) => GEq (AsKnownType term) where
    a `geq` b = do
        -- TODO: there is a HUGE problem here. @EvaluationResult a@ and @a@ have the same string
        -- representation currently, so we need to either fix that or come up with a more sensible
        -- approach, because an attempt to generate a constant application that may fail results in
        -- UNDEFINED BEHAVIOR.
        -- We can probably require each 'KnownType' to be 'Typeable' and avoid checking for equality
        -- string representations here, but this complicates the library.
        guard $ display @String a == display b
        Just $ unsafeCoerce Refl

instance GShow (UniOf term) => GCompare (AsKnownType term) where
    a `gcompare` b
        | Just Refl <- a `geq` b = GEQ
        | otherwise              = liftOrdering $ display @String a `compare` display b

-- | Turn any @proxy a@ into an @AsKnownType a@ provided @a@ is a 'KnownType'.
proxyAsKnownType :: KnownType term a => proxy a -> AsKnownType term a
proxyAsKnownType _ = AsKnownType
