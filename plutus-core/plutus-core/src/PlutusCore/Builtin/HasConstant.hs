{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}

module PlutusCore.Builtin.HasConstant
    ( throwNotAConstant
    , HasConstant (..)
    , HasConstantIn
    ) where

import PlutusCore.Core
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Name

import Control.Monad.Except
import Universe

-- | Throw an 'UnliftingError' saying that the received argument is not a constant.
throwNotAConstant
    :: (MonadError (ErrorWithCause err cause) m, AsUnliftingError err)
    => Maybe cause -> m r
throwNotAConstant = throwingWithCause _UnliftingError "Not a constant"

-- | Ensures that @term@ has a 'Constant'-like constructor to lift values to and unlift values from.
class HasConstant term where
    -- Switching from 'MonadError' to 'Either' here gave us a speedup of 2-4%.
    -- | Unlift from the 'Constant' constructor throwing an 'UnliftingError' if the provided @term@
    -- is not a 'Constant'.
    asConstant
        :: AsUnliftingError err
        => Maybe cause -> term -> Either (ErrorWithCause err cause) (Some (ValueOf (UniOf term)))

    -- | Wrap a Haskell value as a @term@.
    fromConstant :: Some (ValueOf (UniOf term)) -> term

-- | Ensures that @term@ has a 'Constant'-like constructor to lift values to and unlift values from
-- and connects @term@ and its @uni@.
type HasConstantIn uni term = (UniOf term ~ uni, HasConstant term)

instance HasConstant (Term TyName Name uni fun ()) where
    asConstant _        (Constant _ val) = pure val
    asConstant mayCause _                = throwNotAConstant mayCause

    fromConstant = Constant ()
