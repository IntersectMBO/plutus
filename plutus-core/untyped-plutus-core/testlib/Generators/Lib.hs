{-# LANGUAGE TypeOperators #-}

module Generators.Lib where

import Data.Vector qualified as V
import PlutusCore (Name, _nameText)
import PlutusCore.Compiler.Erase (eraseProgram, eraseTerm)
import PlutusCore.Default (Closed, DefaultFun, DefaultUni, Everywhere, GEq)
import PlutusCore.Generators.Hedgehog.AST (AstGen)
import PlutusCore.Generators.Hedgehog.AST qualified as AST
import PlutusPrelude (on, zipExact)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Core.Type (Term (..))

genTerm
  :: forall fun
   . (Bounded fun, Enum fun)
  => AstGen (UPLC.Term Name DefaultUni fun ())
genTerm = fmap eraseTerm AST.genTerm

genProgram
  :: forall fun
   . (Bounded fun, Enum fun) => AstGen (UPLC.Program Name DefaultUni fun ())
genProgram = fmap eraseProgram AST.genProgram

{-| A 'Program' which we compare using textual equality of names
rather than alpha-equivalence.
-}
newtype TextualProgram a = TextualProgram
  { unTextualProgram :: UPLC.Program Name DefaultUni DefaultFun a
  }
  deriving stock Show

instance (Eq a) => Eq (TextualProgram a) where
  (TextualProgram p1) == (TextualProgram p2) = compareProgram p1 p2

compareName :: Name -> Name -> Bool
compareName = (==) `on` _nameText

compareTerm
  :: (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq a)
  => Term Name uni fun a -> Term Name uni fun a -> Bool
compareTerm (Var _ n) (Var _ n') =
  compareName n n'
compareTerm (LamAbs _ n t) (LamAbs _ n' t') =
  compareName n n' && compareTerm t t'
compareTerm (Apply _ t t'') (Apply _ t' t''') =
  compareTerm t t' && compareTerm t'' t'''
compareTerm (Force _ t) (Force _ t') =
  compareTerm t t'
compareTerm (Delay _ t) (Delay _ t') =
  compareTerm t t'
compareTerm (Constant _ x) (Constant _ y) =
  x == y
compareTerm (Builtin _ bi) (Builtin _ bi') =
  bi == bi'
compareTerm (Constr _ i es) (Constr _ i' es') =
  i == i' && maybe False (all (uncurry compareTerm)) (zipExact es es')
compareTerm (Case _ arg cs) (Case _ arg' cs') =
  compareTerm arg arg'
    && case zipExact (V.toList cs) (V.toList cs') of
      Nothing    -> False
      Just pairs -> all (uncurry compareTerm) pairs
compareTerm (Error _) (Error _) = True
compareTerm _ _ = False

compareProgram
  :: (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq a)
  => UPLC.Program Name uni fun a -> UPLC.Program Name uni fun a -> Bool
compareProgram (UPLC.Program _ v t) (UPLC.Program _ v' t') =
  v == v' && compareTerm t t'
