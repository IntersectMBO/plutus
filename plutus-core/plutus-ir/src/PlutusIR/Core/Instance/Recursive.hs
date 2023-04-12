{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-missing-deriving-strategies #-}

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module PlutusIR.Core.Instance.Recursive
    ( -- * Base functors
      TermF (..)
    ) where

import PlutusIR.Core.Type
import PlutusPrelude

import Data.Functor.Foldable.TH

$(join <$> traverse makeBaseFunctor [''Term])
