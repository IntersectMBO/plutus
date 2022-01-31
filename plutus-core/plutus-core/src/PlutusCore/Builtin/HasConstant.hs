{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}

module PlutusCore.Builtin.HasConstant
    ( throwNotAConstant
    , AsConstant (..)
    , FromConstant (..)
    , HasConstant
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

class AsConstant term where
    -- | Unlift from the 'Constant' constructor throwing an 'UnliftingError' if the provided @term@
    -- is not a 'Constant'.
    asConstant
        :: (MonadError (ErrorWithCause err cause) m, AsUnliftingError err)
        => Maybe cause -> term -> m (Some (ValueOf (UniOf term)))

class FromConstant term where
    -- | Wrap a Haskell value as a @term@.
    fromConstant :: Some (ValueOf (UniOf term)) -> term

instance AsConstant (Term TyName Name uni fun ann) where
    asConstant _        (Constant _ val) = pure val
    asConstant mayCause _                = throwNotAConstant mayCause

instance FromConstant (Term tyname name uni fun ()) where
    fromConstant = Constant ()

-- | Ensures that @term@ has a 'Constant'-like constructor to lift values to and unlift values from.
--
-- 'AsConstant' and 'FromConstant' are separate, because we need only one instance of 'AsConstant'
-- per 'Term'-like type and 'FromConstant' requires as many instances as there are different kinds
-- of annotations (we're mostly interested in 'ExMemory' and @()@). Originally we had a single type
-- class but it proved to be less efficient than having two of them.
type HasConstant term = (AsConstant term, FromConstant term)

-- | Ensures that @term@ has a 'Constant'-like constructor to lift values to and unlift values from
-- and connects @term@ and its @uni@.
type HasConstantIn uni term = (UniOf term ~ uni, HasConstant term)
