{-# OPTIONS_GHC -fno-warn-orphans #-}


module Data.Text.PrettyprintM.Doc.Defaults where

import           Data.Text.PrettyprintM.Doc.Core

import           Data.Bifunctor
import           Data.Functor.Const
import           Data.Functor.Identity
import           Data.Int
import           Data.List.NonEmpty
import           Data.Maybe
import           Data.Proxy
import qualified Data.Text                       as Strict
import qualified Data.Text.Lazy                  as Lazy
import           Data.Text.Prettyprint.Doc
import           Data.Void
import           Data.Word
import           GHC.Natural

-- ********************************************************
-- **  **
-- ********************************************************
