{-# LANGUAGE OverloadedStrings #-}

module Analysis.Spec.Lib where

import PlutusCore.Builtin (BuiltinSemanticsVariant)
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Default.Builtins (DefaultFun (AddInteger))
import PlutusCore.MkPlc (mkConstant, mkIterAppNoAnn)
import PlutusCore.Name.Unique (Name)
import PlutusCore.Pretty (prettyPlcReadable)
import PlutusCore.Quote (freshName, runQuote)
import PlutusPrelude (def)
import Test.Tasty.Extras (TestNested, nestedGoldenVsDoc)
import UntypedPlutusCore.Core.Type (Term (Apply, Builtin, Constr, LamAbs, Var))
import UntypedPlutusCore.Purity (termEvaluationOrder)

-- that the computation is lazy
-- [ [ n m ] (constr 1 [undefined]) ]
dangerTerm :: Term Name DefaultUni DefaultFun ()
dangerTerm = runQuote $ do
  n <- freshName "n"
  m <- freshName "m"
  -- The UPLC term type is strict, so it's hard to hide an undefined in there
  -- Take advantage of the fact that it's still using lazy lists for constr
  -- arguments for now.
  pure $ Apply () (Apply () (Var () n) (Var () m)) (Constr () 1 [undefined])

letFun :: Term Name DefaultUni DefaultFun ()
letFun = runQuote $ do
  n <- freshName "n"
  let intConst = mkConstant () (1 :: Integer)
  pure $
    Apply
      ()
      (LamAbs () n (mkIterAppNoAnn (Var () n) [intConst, intConst]))
      (Builtin () AddInteger)

letImpure :: Term Name DefaultUni DefaultFun ()
letImpure = runQuote $ do
  n <- freshName "n"
  m <- freshName "m"
  let intConst = mkConstant () (1 :: Integer)
  pure $
    Apply
      ()
      (LamAbs () n (mkIterAppNoAnn (Var () n) [intConst, intConst]))
      -- don't need this to be well-scoped
      (Apply () (Var () m) intConst)

builtinSemantics :: BuiltinSemanticsVariant DefaultFun
builtinSemantics = def

goldenEvalOrder :: String -> Term Name DefaultUni DefaultFun () -> TestNested
goldenEvalOrder name tm =
  let order = termEvaluationOrder builtinSemantics tm
   in nestedGoldenVsDoc name "" (prettyPlcReadable order)
