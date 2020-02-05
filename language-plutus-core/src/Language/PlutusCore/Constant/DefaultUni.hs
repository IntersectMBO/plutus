-- Appears in generated instances.
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Constant.DefaultUni
    ( ByteString16 (..)
    , DefaultUni (..)
    , HasDefaultUni
    ) where

import           Language.PlutusCore.Constant.Universe

import qualified Data.ByteString.Lazy                  as BSL
import           Data.GADT.Compare.TH
import           Data.GADT.Show.TH
import           Language.Haskell.TH.Syntax            (Lift)

-- TODO: use strict bytestrings.
newtype ByteString16 = ByteString16
    { unByteString16 :: BSL.ByteString
    } deriving newtype (Eq, Ord)

data DefaultUni a where
    DefaultUniInteger    :: DefaultUni Integer
    DefaultUniByteString :: DefaultUni ByteString16
    DefaultUniChar       :: DefaultUni Char
    DefaultUniString     :: DefaultUni String

deriveGEq   ''DefaultUni
deriveGShow ''DefaultUni
deriving instance Lift (DefaultUni a)

instance DefaultUni `Includes` Integer         where knownUni = DefaultUniInteger
instance DefaultUni `Includes` ByteString16    where knownUni = DefaultUniByteString
instance DefaultUni `Includes` Char            where knownUni = DefaultUniChar
instance a ~ Char => DefaultUni `Includes` [a] where knownUni = DefaultUniString

instance Closed DefaultUni where
    type DefaultUni `Everywhere` constr =
        ( constr Integer
        , constr ByteString16
        , constr Char
        , constr String
        )

    tagOf DefaultUniInteger    = 0
    tagOf DefaultUniByteString = 1
    tagOf DefaultUniString     = 2
    tagOf DefaultUniChar       = 3

    uniAt 0 = Just $ Some DefaultUniInteger
    uniAt 1 = Just $ Some DefaultUniByteString
    uniAt 2 = Just $ Some DefaultUniString
    uniAt 3 = Just $ Some DefaultUniChar
    uniAt _ = Nothing

    bring _ DefaultUniInteger    = id
    bring _ DefaultUniByteString = id
    bring _ DefaultUniString     = id
    bring _ DefaultUniChar       = id

type HasDefaultUni uni = DefaultUni `Everywhere` Includes uni
