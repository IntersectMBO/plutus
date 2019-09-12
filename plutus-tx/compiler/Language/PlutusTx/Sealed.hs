{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
-- This is a separate module so we can ensure it gets an interface file,
-- whereas we try and prevent that for the main Builtins module.
module Language.PlutusTx.Sealed (Sealed, seal, unseal) where

{-# ANN module "HLint: ignore"#-}

{- Note [Sealed]
'Sealed' is essentially just a box. However, by differentially exposing
'seal' and 'unseal', we can make it so that only certain people can
box things up, or unbox things. This lets us enforce security properties
such as "this script can only pass Sealed values around but cannot create
or modify them".

To do this properly, we need to make 'Sealed' and its associated functions (extensible)
builtins. But this isn't working yet, so for now we fake it in userspace so
we can make the interface changes.
-}
data Sealed a = Seal { unSeal :: a }

-- Not actually being mapped to a builtin, this is a normal function that we
-- should have an unfolding for. See Note [Sealed]
{-# INLINABLE seal #-}
-- | Seal a value into a 'Sealed'.
seal :: a -> Sealed a
seal = Seal

-- Not actually being mapped to a builtin, this is a normal function that we
-- should have an unfolding for. See Note [Sealed]
{-# INLINABLE unseal #-}
-- | Unseal a value inside a 'Sealed'.
unseal :: Sealed a -> a
unseal = unSeal
