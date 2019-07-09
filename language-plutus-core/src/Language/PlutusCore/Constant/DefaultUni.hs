{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Language.PlutusCore.Constant.DefaultUni
    ( HasDefaultUni
    , DefaultUni (..)
    ) where

import           Language.PlutusCore.Constant.Universe

import qualified Data.ByteString.Lazy                  as BSL
import           Data.GADT.Compare.TH

type HasDefaultUni uni =
    ( uni `Includes` Integer
    , uni `Includes` BSL.ByteString
    , uni `Includes` String
    )

data DefaultUni a where
    DefaultUniInteger    :: DefaultUni Integer
    DefaultUniByteString :: DefaultUni BSL.ByteString
    DefaultUniString     :: DefaultUni String

deriveGEq ''DefaultUni

instance DefaultUni `Includes` Integer where
    knownUni = DefaultUniInteger
instance DefaultUni `Includes` BSL.ByteString where
    knownUni = DefaultUniByteString
instance a ~ Char => DefaultUni `Includes` [a] where
    knownUni = DefaultUniString

instance GShow DefaultUni where
    gshow DefaultUniInteger    = "DefaultUniInteger"
    gshow DefaultUniByteString = "DefaultUniByteString"
    gshow DefaultUniString     = "DefaultUniString"

instance Closed DefaultUni where
    type Everywhere DefaultUni constr = (constr Integer, constr BSL.ByteString, constr String)
    bring _ DefaultUniInteger    = id
    bring _ DefaultUniByteString = id
    bring _ DefaultUniString     = id
