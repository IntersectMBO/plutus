{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusCore.Builtin.HasConstant
    ( KnownTypeError (..)
    , throwNotAConstant
    , HasConstant (..)
    , HasConstantIn
    , fromValueOf
    , fromValue
    ) where

import PlutusCore.Core
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Name

import Universe

{- Note [Existence of HasConstant]
We don't really need 'HasConstant' and could get away with only having 'HasConstantIn', however
defining the latter directly as a @class@ instead of a type synonym in terms of the former is
detrimental to performance, see the comments in https://github.com/input-output-hk/plutus/pull/4417

This is likely due to the same reason as in 'mkMachineParameters',
see Note [The equality constraint in mkMachineParameters].
-}

-- See Note [Existence of HasConstant].
-- We name it @term@ rather than @val@, because various @Term@ (UPLC/TPLC/PIR) data types have
-- 'Constant'-like constructors too and we lift to / unlift from those in tests.
-- | Ensures that @term@ has a 'Constant'-like constructor to lift values to and unlift values from.
class HasConstant term where
    -- Switching from 'MonadError' to 'Either' here gave us a speedup of 2-4%.
    -- | Unwrap from a 'Constant'-like constructor throwing an 'UnliftingError' if the provided
    -- @term@ is not a wrapped Haskell value.
    asConstant :: term -> Either KnownTypeError (Some (ValueOf (UniOf term)))

    -- | Wrap a Haskell value as a @term@.
    fromConstant :: Some (ValueOf (UniOf term)) -> term

-- | Ensures that @term@ has a 'Constant'-like constructor to lift values to and unlift values from
-- and connects @term@ and its @uni@.
type HasConstantIn uni term = (UniOf term ~ uni, HasConstant term)

-- | Wrap a Haskell value (given its explicit type tag) as a @term@.
fromValueOf :: HasConstant term => UniOf term (Esc a) -> a -> term
fromValueOf uni = fromConstant . someValueOf uni
{-# INLINE fromValueOf #-}

-- | Wrap a Haskell value (provided its type is in the universe) as a @term@.
fromValue :: (HasConstant term, UniOf term `HasTermLevel` a) => a -> term
fromValue = fromValueOf knownUni
{-# INLINE fromValue #-}

instance HasConstant (Term TyName Name uni fun ()) where
    asConstant (Constant _ val) = pure val
    asConstant _                = throwNotAConstant

    fromConstant = Constant ()
