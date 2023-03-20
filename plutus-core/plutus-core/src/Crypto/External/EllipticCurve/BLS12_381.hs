-- FIXME. This is a local copy of
-- https://github.com/input-output-hk/cardano-base/tree/bls12-381, which
-- currently has an open PR.  Once that is merged we should delete this and
-- depend on the code in cardano-base instead.  There may be a dnager of
-- confusion when we do that because we've got module names beginning with
-- `Crypto.` as well.

--- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
module Crypto.External.EllipticCurve.BLS12_381
(
  -- * Types
    Point
  , Point1
  , Point2
  , PT
  , Curve1
  , Curve2
  , BLSTError (..)

  -- * BLS Class
  , BLS

  -- * Point / Group operations
  -- | These work on both curves, and take phantom parameters of type 'Curve1'
  -- or 'Curve2' to select one of the two provided elliptic curves.
  , blsInGroup
  , blsAddOrDouble
  , blsMult
  , blsCneg
  , blsNeg
  , blsCompress
  , blsSerialize
  , blsUncompress
  , blsDeserialize
  , blsHash
  , blsGenerator
  , blsIsInf

  -- * PT operations
  , ptMult
  , ptFinalVerify

  -- * Pairings
  , millerLoop

  -- * The period (modulo) of scalars
  , scalarPeriod
)
where

import Crypto.External.EllipticCurve.BLS12_381.Internal
