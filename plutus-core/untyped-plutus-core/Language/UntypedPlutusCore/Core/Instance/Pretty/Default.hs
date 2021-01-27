-- | While the flexible pretty-printing infrastructure is useful when you want it,
-- it's helpful to have an implementation of the default Pretty typeclass that
-- does the default thing.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.UntypedPlutusCore.Core.Instance.Pretty.Default () where

import           PlutusPrelude

import           Language.PlutusCore.Pretty.Classic
import           Language.PlutusCore.Pretty.PrettyConst
import           Language.PlutusCore.Universe
import           Language.UntypedPlutusCore.Core.Instance.Pretty.Classic ()
import           Language.UntypedPlutusCore.Core.Type

instance
        ( PrettyClassic name
        , GShow uni, Closed uni, uni `Everywhere` PrettyConst, Pretty fun
        ) => Pretty (Term name uni fun ann) where
    pretty = prettyClassicDef

instance
        ( PrettyClassic name
        , GShow uni, Closed uni, uni `Everywhere` PrettyConst, Pretty fun
        ) => Pretty (Program name uni fun ann) where
    pretty = prettyClassicDef
