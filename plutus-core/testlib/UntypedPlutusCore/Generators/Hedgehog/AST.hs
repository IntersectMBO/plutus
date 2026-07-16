module UntypedPlutusCore.Generators.Hedgehog.AST
  ( regenConstantsUntil
  , PLC.AstGen
  , PLC.runAstGen
  , PLC.genVersion
  , genTerm
  , genProgram
  , mangleNames
  ) where

import PlutusPrelude

import PlutusCore.Generators.Hedgehog.AST qualified as PLC

import PlutusCore.Compiler.Erase
import UntypedPlutusCore as UPLC

import Data.Set.Lens (setOf)
import Hedgehog
import Universe

regenConstantsUntil
  :: MonadGen m
  => (Some (ValueOf DefaultUni) -> Bool)
  -> Program name DefaultUni fun DefaultBuiltinPattern ann
  -> m (Program name DefaultUni fun DefaultBuiltinPattern ann)
regenConstantsUntil p =
  progTerm . termSubstConstantsM $ \ann -> fmap (fmap $ Constant ann) . PLC.regenConstantUntil p

genTerm
  :: forall fun
   . (Bounded fun, Enum fun)
  => PLC.AstGen (Term Name DefaultUni fun DefaultBuiltinPattern ())
genTerm = fmap eraseTerm PLC.genTerm

genProgram
  :: forall fun
   . (Bounded fun, Enum fun)
  => PLC.AstGen (Program Name DefaultUni fun DefaultBuiltinPattern ())
genProgram = fmap eraseProgram PLC.genProgram

-- See Note [Name mangling]
mangleNames
  :: Term Name DefaultUni DefaultFun DefaultBuiltinPattern ()
  -> PLC.AstGen (Maybe (Term Name DefaultUni DefaultFun DefaultBuiltinPattern ()))
mangleNames term = do
  mayMang <- PLC.genNameMangler $ setOf vTerm term
  for mayMang $ \mang -> termSubstNamesM (const . fmap (fmap $ UPLC.Var ()) . mang) term
