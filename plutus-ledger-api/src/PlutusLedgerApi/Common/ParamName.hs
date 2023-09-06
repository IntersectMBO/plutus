-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusLedgerApi.Common.ParamName
    ( IsParamName (..)
    , GenericParamName (..)
    , toCostModelParams
    , tagWithParamNames
    , CostModelApplyError (..)
    , CostModelApplyWarn (..)
    ) where

import PlutusCore.Evaluation.Machine.CostModelInterface

import Control.Monad.Except
import Control.Monad.Writer.Strict
import Data.Bifunctor
import Data.Char (toLower)
import Data.List.Extra
import Data.Map as Map
import Data.Text qualified as Text
import GHC.Generics

{-| A parameter name for different plutus versions.

Each Plutus version should expose such an enumeration as an ADT and create
an instance of 'ParamName' out of it.

A valid parameter name has to be enumeration, bounded, ordered, and
prettyprintable to a \"lower-Kebab\" string.
-}
class IsParamName a where
   -- | Take the raw textual form for a given typed-by-plutus-version cost model parameter
   -- Any implementation *must be* an injective function.
   -- The 'GIsParamName' generic implementation guarantees injection.
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

-- | Given an ordered list of parameter values, tag them with their parameter
-- names.  If the passed parameter values are more than expected: the function
-- will ignore the extraneous values at the tail of the list, if the passed
-- values are less than expected: the function will throw an error; for more
-- information, see Note [Cost model parameters from the ledger's point of view]
tagWithParamNames :: forall k m. (Enum k, Bounded k,
                            MonadError CostModelApplyError m,
                            -- OPTIMIZE: MonadWriter.CPS is probably better than MonadWriter.Strict but needs mtl>=2.3
                            -- OPTIMIZE: using List [] as the log datatype is worse than others (DList/Endo) but does not matter much here
                            MonadWriter [CostModelApplyWarn] m)
                  => [Integer] -> m [(k, Integer)]
tagWithParamNames ledgerParams =
    let paramNames = enumerate @k
        lenExpected = length paramNames
        lenActual = length ledgerParams
    in case lenExpected `compare` lenActual of
        EQ ->
            pure $ zip paramNames ledgerParams
        LT -> do
            -- See Note [Cost model parameters from the ledger's point of view]
            tell [CMTooManyParamsWarn {cmTooManyExpected = lenExpected, cmTooManyActual = lenActual}]
            -- zip will truncate/ignore any extraneous parameter values
            pure $ zip paramNames ledgerParams
        GT ->
            -- See Note [Cost model parameters from the ledger's point of view]
            throwError $ CMTooFewParamsError {cmTooFewExpected = lenExpected, cmTooFewActual = lenActual }

-- | Untags the plutus version from the typed cost model parameters and returns their raw textual form
-- (internally used by CostModelInterface).
toCostModelParams :: IsParamName k => [(k, Integer)] -> CostModelParams
toCostModelParams = Map.fromList . fmap (first $ Text.pack . showParamName)
