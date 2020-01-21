-- appears in the generated instances
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Evaluation.Error where

import           PlutusPrelude

import           Language.PlutusCore.Core
import           Language.PlutusCore.Name

import           Control.Lens.TH
import           Data.String
import           Data.Text                (Text)

newtype UnliftingError
    = UnliftingErrorE Text
    deriving (Show, Eq)
    deriving newtype (IsString)
makeClassyPrisms ''UnliftingError

-- | The type of constant applications errors.
data ConstAppError
    = ExcessArgumentsConstAppError [Value TyName Name ()]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments.
    | UnliftingConstAppError UnliftingError
      -- ^ Could not construct denotation for a builtin.
    deriving (Show, Eq)
makeClassyPrisms ''ConstAppError

instance AsUnliftingError ConstAppError where
    _UnliftingError = _UnliftingConstAppError

instance Pretty UnliftingError where
    pretty (UnliftingErrorE err) = fold
        [ "Could not unlift a builtin:", "\n"
        , pretty err
        ]

instance PrettyBy config (Term TyName Name ()) => PrettyBy config ConstAppError where
    prettyBy config (ExcessArgumentsConstAppError args) = fold
        [ "A constant applied to too many arguments:", "\n"
        , "Excess ones are: ", prettyBy config args
        ]
    prettyBy _      (UnliftingConstAppError err) = pretty err
