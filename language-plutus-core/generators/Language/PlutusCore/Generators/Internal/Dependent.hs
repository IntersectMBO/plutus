-- | Orphan 'GEq' and 'GCompare' instances of data types from "Language.PlutusCore.Constant.Typed".
-- The reason we keep the instances separate is that they are highly unsafe ('unsafeCoerce' is used)
-- and needed only for tests.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE GADTs #-}

module Language.PlutusCore.Generators.Internal.Dependent
    ( AsKnownType (..)
    , proxyAsKnownType
    ) where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Pretty

import           Control.Monad
import           Data.GADT.Compare
import           Unsafe.Coerce

liftOrdering :: Ordering -> GOrdering a b
liftOrdering LT = GLT
liftOrdering EQ = error "'liftOrdering': 'Eq'"
liftOrdering GT = GGT

-- | Contains a proof that @a@ is a 'KnownType'.
data AsKnownType a where
    AsKnownType :: KnownType a => AsKnownType a

instance Pretty (AsKnownType a) where
    pretty a@AsKnownType = pretty $ toTypeAst a

instance GEq AsKnownType where
    a `geq` b = do
        -- TODO: there is a HUGE problem here. @EvaluationResult a@ and @a@ have the same string
        -- representation currently, so we need to either fix that or come up with a more sensible
        -- approach, because an attempt to generate a constant application that may fail results in
        -- UNDEFINED BEHAVIOR.
        -- We can probably require each 'KnownType' to be 'Typeable' and avoid checking for equality
        -- string representations here, but this complicates the library.
        guard $ prettyString a == prettyString b
        Just $ unsafeCoerce Refl

instance GCompare AsKnownType where
    a `gcompare` b
        | Just Refl <- a `geq` b = GEQ
        | otherwise              = liftOrdering $ prettyString a `compare` prettyString b

-- | Turn any @proxy a@ into an @AsKnownType a@ provided @a@ is a 'KnownType'.
proxyAsKnownType :: KnownType a => proxy a -> AsKnownType a
proxyAsKnownType _ = AsKnownType
