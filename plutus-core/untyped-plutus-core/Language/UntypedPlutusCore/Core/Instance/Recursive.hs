{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module Language.UntypedPlutusCore.Core.Instance.Recursive
    ( -- * Base functors
      TermF (..)
    ) where

import           Language.UntypedPlutusCore.Core.Type

import           Data.Functor.Foldable.TH

$(makeBaseFunctor ''Term)
