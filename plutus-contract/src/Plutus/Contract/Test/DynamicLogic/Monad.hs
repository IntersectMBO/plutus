{-# LANGUAGE FlexibleContexts #-}
module Plutus.Contract.Test.DynamicLogic.Monad
    ( DL
    , action
    , anyAction
    , anyActions
    , anyActions_
    , stopping
    , weight
    , getModelStateDL
    , assert
    , assertModel
    , monitorDL
    , forAllQ
    , forAllDL
    , forAllMappedDL
    , withDLTest
    , DL.DynLogic
    , DL.DynLogicModel(..)
    , DL.DynLogicTest(..)
    , DL.TestStep(..)
    , module Plutus.Contract.Test.DynamicLogic.Quantify
    ) where

import           Control.Applicative
import           Control.Monad
import           Data.Typeable

import qualified Plutus.Contract.Test.DynamicLogic          as DL
import           Plutus.Contract.Test.DynamicLogic.Quantify
import           Plutus.Contract.Test.StateModel

import           Test.QuickCheck

-- | The `DL` monad provides a nicer interface to dynamic logic formulae than the plain API.
--   It's a continuation monad producing a `DL.DynLogic` formula, with a state component threaded
--   through.
newtype DL s a = DL { unDL :: s -> (a -> s -> DL.DynLogic s) -> DL.DynLogic s }
    deriving (Functor)

instance Applicative (DL s) where
    pure x = DL $ \ s k -> k x s
    (<*>)  = ap

instance Monad (DL s) where
    return = pure
    DL h >>= j = DL $ \ s k -> h s $ \ x s1 -> unDL (j x) s1 k

action :: (Show a, Typeable a, Eq (Action s a)) => Action s a -> DL s ()
action cmd = DL $ \ _ k -> DL.after cmd $ k ()

anyAction :: DL s ()
anyAction = DL $ \ _ k -> DL.afterAny $ k ()

anyActions :: Int -> DL s ()
anyActions n = stopping <|> weight (1 / fromIntegral n)
                        <|> (anyAction >> anyActions n)

anyActions_ :: DL s ()
anyActions_ = stopping <|> (anyAction >> anyActions_)

stopping :: DL s ()
stopping = DL $ \ s k -> DL.toStop (k () s)

weight :: Double -> DL s ()
weight w = DL $ \ s k -> DL.weight w (k () s)

getModelStateDL :: DL s s
getModelStateDL = DL $ \ s k -> k s s

errorDL :: String -> DL s a
errorDL name = DL $ \ _ _ -> DL.errorDL name

-- | Fail if the boolean is @False@.
--
--   Equivalent to
--
-- @
-- assert msg b = unless b (fail msg)
-- @
assert :: String -> Bool -> DL s ()
assert name b = if b then return () else errorDL name

assertModel :: String -> (s -> Bool) -> DL s ()
assertModel name p = assert name . p =<< getModelStateDL

monitorDL :: (Property -> Property) -> DL s ()
monitorDL f = DL $ \s k -> DL.monitorDL f (k () s)

-- | Generate a random value using the given `Quantification` (or list/tuple of quantifications).
--   Generated values will only shrink to smaller values that could also have been generated.
forAllQ :: Quantifiable q => q -> DL s (Quantifies q)
forAllQ q = DL $ \ s k -> DL.forAllQ q $ \ x -> k x s

instance Alternative (DL s) where
    empty = DL $ \ _ _ -> DL.ignore
    DL h <|> DL j = DL $ \ s k -> h s k DL.||| j s k

instance MonadFail (DL s) where
    fail = errorDL

runDL :: s -> DL s () -> DL.DynLogic s
runDL s dl = unDL dl s $ \ _ _ -> DL.passTest

forAllDL :: (DL.DynLogicModel s, Testable a) =>
            DL s () -> (Actions s -> a) -> Property
forAllDL d prop = DL.forAllScripts (runDL initialState d) prop

forAllMappedDL ::
  (DL.DynLogicModel s, Testable a, Show rep) =>
    (rep -> DL.DynLogicTest s) -> (DL.DynLogicTest s -> rep) -> (Actions s -> srep)
      -> DL s () -> (srep -> a) -> Property
forAllMappedDL to from fromScript d prop =
  DL.forAllMappedScripts to from (runDL initialState d) (prop . fromScript)

withDLTest :: (DL.DynLogicModel s, Testable a) => DL s () -> (Actions s -> a) -> DL.DynLogicTest s -> Property
withDLTest d prop test = DL.withDLScriptPrefix (runDL initialState d) prop test

