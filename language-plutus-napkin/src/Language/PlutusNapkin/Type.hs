{-# LANGUAGE DeriveFunctor #-}

module Language.PlutusNapkin.Type ( PlutusNapkinF (..)
                                  , PlutusNapkin
                                  , Fix (..)
                                  ) where

import qualified Data.ByteString.Lazy as BSL

-- | Base functor for Plutus Napkin expressions
data PlutusNapkinF a x = PNByteString a BSL.ByteString
                       | PNInt a Int
                       | PNFloat a Float
                       | Let a x x
                       deriving (Functor)

newtype Fix f = Fix { unFix :: f (Fix f) }

-- | Annotated type for Plutus Napkin expressions.
type PlutusNapkin a = Fix (PlutusNapkinF a)
