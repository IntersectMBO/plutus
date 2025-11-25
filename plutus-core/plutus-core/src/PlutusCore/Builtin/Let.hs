{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusCore.Builtin.Let where

import PlutusCore.Builtin.KnownType (Spine)
import PlutusCore.Core.Type (Type, UniOf)
import PlutusCore.Name.Unique (TyName)

import Control.DeepSeq (NFData (..), rwhnf)
import Data.Default.Class (Default (..))
import Data.Text (Text)
import Data.Vector (Vector)
import NoThunks.Class
import Text.PrettyBy (display)
import Universe


class LetBuiltin uni where
    -- | Given a constant with its type tag and a vector of branches, choose the appropriate branch
    -- or fail if the constant doesn't correspond to any of the branches (or casing on constants of
    -- this type isn't supported at all).
    letBuiltin
        :: Some (ValueOf uni)
        -> Either Text [Some (ValueOf uni)]

data LeterBuiltin uni = LeterBuiltin
    { unLeterBuiltin :: !(Some (ValueOf uni) -> Either Text [Some (ValueOf uni)])
    }

instance NFData (LeterBuiltin uni) where
    rnf = rwhnf

deriving via OnlyCheckWhnfNamed "PlutusCore.Builtin.Case.LeterBuiltin" (LeterBuiltin uni)
    instance NoThunks (LeterBuiltin uni)

instance LetBuiltin uni => Default (LeterBuiltin uni) where
    def = LeterBuiltin letBuiltin

unavailableLeterBuiltin :: Int -> LeterBuiltin uni
unavailableLeterBuiltin ver =
    LeterBuiltin $ \_ -> Left $
        "'let' TODO " <> display ver
