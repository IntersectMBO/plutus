{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusIR.Pass.Test where

import Control.Monad.Except
import Data.Typeable
import PlutusCore qualified as PLC
import PlutusCore.Builtin
import PlutusCore.Generators.QuickCheck (forAllDoc)
import PlutusCore.Pretty qualified as PLC
import PlutusIR.Core.Type
import PlutusIR.Error qualified as PIR
import PlutusIR.Generators.QuickCheck
import PlutusIR.Pass
import PlutusIR.TypeCheck
import PlutusIR.TypeCheck qualified as TC
import PlutusPrelude
import Test.QuickCheck

-- Convert Either Error () to Either String () to match with the Testable (Either String ())
-- instance.
convertToEitherString
  :: Either (PIR.Error PLC.DefaultUni PLC.DefaultFun ()) ()
  -> Either String ()
convertToEitherString = \case
  Left err -> Left $ show err
  Right () -> Right ()

instance Arbitrary (BuiltinSemanticsVariant PLC.DefaultFun) where
  arbitrary = elements enumerate

{-| An appropriate number of tests for a compiler pass property, so that we get some decent
exploration of the program space. If you also take other arguments, then consider multiplying
this up in order to account for the larger space. -}
numTestsForPassProp :: Int
numTestsForPassProp = 99

-- | Run a 'Pass' on a 'Term', setting up the typechecking config and throwing errors.
runTestPass
  :: ( PLC.ThrowableBuiltins uni fun
     , PLC.Typecheckable uni fun
     , PLC.Pretty a
     , Typeable a
     , Monoid a
     , Monad m
     )
  => (TC.PirTCConfig uni fun -> Pass m tyname name uni fun a)
  -> Term tyname name uni fun a
  -> m (Term tyname name uni fun a)
runTestPass pass t = do
  res <- runExceptT $ do
    tcconfig <- modifyError PIR.PLCTypeError $ TC.getDefTypeCheckConfig mempty
    runPass (\_ -> pure ()) True (pass tcconfig) t
  case res of
    Left e -> throw e
    Right v -> pure v

{-| Run a 'Pass' on generated 'Terms's, setting up the typechecking config
and throwing errors. -}
testPassProp
  :: Monad m
  => (forall a. m a -> a)
  -> ( TC.PirTCConfig PLC.DefaultUni PLC.DefaultFun
       -> Pass m TyName Name PLC.DefaultUni PLC.DefaultFun ()
     )
  -> Property
testPassProp exitMonad pass =
  testPassProp'
    ()
    id
    after
    pass
  where
    after res = convertToEitherString $ first void $ exitMonad $ runExceptT res

{-| A version of 'testPassProp' with more control, allowing some pre-processing
of the term, and a more specific "exit" function. -}
testPassProp'
  :: forall m tyname name a prop
   . (Monad m, Testable prop)
  => a
  -> ( Term TyName Name PLC.DefaultUni PLC.DefaultFun ()
       -> Term tyname name PLC.DefaultUni PLC.DefaultFun a
     )
  -> (ExceptT (PIR.Error PLC.DefaultUni PLC.DefaultFun a) m () -> prop)
  -> ( TC.PirTCConfig PLC.DefaultUni PLC.DefaultFun
       -> Pass m tyname name PLC.DefaultUni PLC.DefaultFun a
     )
  -> Property
testPassProp' ann before after pass =
  forAllDoc "ty,tm" genTypeAndTerm_ shrinkClosedTypedTerm $ \(_ty, tm) ->
    let
      res :: ExceptT (PIR.Error PLC.DefaultUni PLC.DefaultFun a) m ()
      res = do
        tcconfig <- modifyError PIR.PLCTypeError $ getDefTypeCheckConfig ann
        let tm' = before tm
        _ <- runPass (\_ -> pure ()) True (pass tcconfig) tm'
        pure ()
     in
      after res
