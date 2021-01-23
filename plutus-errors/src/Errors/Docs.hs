{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE PolyKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_HADDOCK ignore-exports #-}
-- | All the Plutus errors project-wide, indexed by their error code.
module Errors.Docs () where

import           Errors.TH.GenDocs

genDocs
