{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}

module PlutusCore.Builtin.HasConstant
    ( KnownTypeError (..)
    , throwNotAConstant
    , HasConstant (..)
    , HasConstantIn
    ) where

import PlutusCore.Core
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Name

import Universe

-- | Ensures that @term@ has a 'Constant'-like constructor to lift values to and unlift values from.
class HasConstant term where
    -- Switching from 'MonadError' to 'Either' here gave us a speedup of 2-4%.
    -- | Unlift from the 'Constant' constructor throwing an 'UnliftingError' if the provided @term@
    -- is not a 'Constant'.
    asConstant :: term -> Either KnownTypeError (Some (ValueOf (UniOf term)))

    -- | Wrap a Haskell value as a @term@.
    fromConstant :: Some (ValueOf (UniOf term)) -> term

-- | Ensures that @term@ has a 'Constant'-like constructor to lift values to and unlift values from
-- and connects @term@ and its @uni@.
type HasConstantIn uni term = (UniOf term ~ uni, HasConstant term)

instance HasConstant (Term TyName Name uni fun ()) where
    asConstant (Constant _ val) = pure val
    asConstant _                = throwNotAConstant

    fromConstant = Constant ()
