{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module UntypedPlutusCore.Core.Instance.Recursive
    ( -- * Base functors
      TermF (..)
    ) where

import           UntypedPlutusCore.Core.Type

import           Data.Functor.Foldable.TH

$(makeBaseFunctor ''Term)
