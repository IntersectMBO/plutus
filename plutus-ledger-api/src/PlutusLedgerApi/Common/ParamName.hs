-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusLedgerApi.Common.ParamName where

import PlutusCore.Evaluation.Machine.CostModelInterface

import Control.Monad.Except
import Data.Bifunctor
import Data.Char (toLower)
import Data.List.Extra
import Data.Map as Map
import Data.Text qualified as Text
import GHC.Generics

{-| A valid parameter name has to be enumeration, bounded, ordered, and
prettyprintable in a "lowerKebab" way.

Each API version should expose such an enumeration as an ADT and create
an instance of ParamName out of it.
-}
class IsParamName a where
   showParamName :: a -> String

-- | A Generic wrapper for use with deriving via
newtype GenericParamName a = GenericParamName a

instance (Generic a, GIsParamName (Rep a)) => IsParamName (GenericParamName a) where
   showParamName (GenericParamName a) = gshowParamName $ from a

-- | A datatype-generic class to prettyprint 'sums of nullary constructors' in lower-kebab syntax.
class GIsParamName f where
    gshowParamName :: f p -> String

instance (GIsParamName a) => GIsParamName (M1 D i a) where
    gshowParamName (M1 x) = gshowParamName x

{- Note [Quotation marks in cost model parameter constructors]
We use the quotation mark <'> inside each nullary constructor of
a cost parameter name as a delimiter of sections when lowerKebab-prettyprinting.
The character <_> cannot be used as a delimiter because it may be part of the builtin's name (sha2_256,etc).
-}

instance Constructor i => GIsParamName (M1 C i U1) where
    gshowParamName = lowerKebab . conName
      where
        lowerKebab :: String -> String
        lowerKebab (h:t) = toLower h : fmap maybeKebab t
        lowerKebab _     = error "this should not happen because constructors cannot have empty names"

        maybeKebab '\'' = '-'
        maybeKebab c    = c


instance (GIsParamName a, GIsParamName b) => GIsParamName ((:+:) a b) where
    gshowParamName (L1 x) = gshowParamName x
    gshowParamName (R1 x) = gshowParamName x

-- Given an ordered list of parameter values, tag them with their parameter names.
tagWithParamNames :: forall k m. (Enum k, Bounded k, MonadError CostModelApplyError m) => [Integer] -> m [(k, Integer)]
tagWithParamNames ledgerParams =
    let paramNames = enumerate @k
        lenActual = length ledgerParams
        lenExpected = length paramNames
    in if lenActual /= lenExpected
       then throwError $ CMWrongNumberOfParams lenExpected lenActual
       else pure $ zip paramNames ledgerParams


-- | Essentially untag the association of param names to values
-- so that CostModelInterface can make use of it.
toCostModelParams :: IsParamName k => [(k, Integer)] -> CostModelParams
toCostModelParams = Map.fromList . fmap (first $ Text.pack . showParamName)
