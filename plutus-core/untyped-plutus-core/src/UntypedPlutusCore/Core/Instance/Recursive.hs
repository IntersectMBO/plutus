{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-missing-deriving-strategies #-}

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module UntypedPlutusCore.Core.Instance.Recursive
    ( -- * Base functors
      TermF (..)
    ) where

import UntypedPlutusCore.Core.Type

import Data.Functor.Foldable.TH

$(makeBaseFunctor ''Term)
