{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Generators.PIR.Utils where

import Prettyprinter

import Control.Monad.Reader

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Set.Lens (setOf)
import Data.String
import Test.QuickCheck

import PlutusCore.Default
import PlutusCore.MkPlc hiding (error)
import PlutusCore.Name
import PlutusCore.Pretty
import PlutusIR
import PlutusIR.Compiler.Datatype
import PlutusIR.Subst

import PlutusCore.Generators.PIR.GenTm
import PlutusIR.Core.Instance.Pretty.Readable

-- | Show a `Doc` when a property fails.
ceDoc :: Testable t => Doc ann -> t -> Property
ceDoc d = counterexample (render d)

-- | Bind a value to a name in a property so that
-- it is displayed as a `name = thing` binding if the
-- property fails.
letCE :: (PrettyPir a, Testable p)
      => String
      -> a
      -> (a -> p)
      -> Property
letCE name x k = ceDoc (fromString name <+> "=" <+> prettyPirReadable x) (k x)

-- | Like `forAllShrink` but displays the bound value as
-- a named pretty-printed binding like `letCE`
forAllDoc :: (PrettyPir a, Testable p)
          => String
          -> Gen a
          -> (a -> [a])
          -> (a -> p)
          -> Property
forAllDoc name g shr k =
  forAllShrinkBlind g shr $ \ x ->
    ceDoc (fromString name <+> "=" <+> prettyPirReadable x)
          (k x)

-- | Check that a list of potential counterexamples is empty and display the
-- list as a QuickCheck counterexample if its not.
assertNoCounterexamples :: PrettyPir a => [a] -> Property
assertNoCounterexamples []  = property True
assertNoCounterexamples bad = ceDoc (prettyPirReadable bad) False

-- * Dealing with fresh names

-- | Get the free type variables in a type along with how many
-- times they occur. The elements of the map are guaranteed to be
-- non-zero.
fvTypeBag :: Type TyName DefaultUni () -> Map TyName Int
fvTypeBag ty = case ty of
  TyVar _ x        -> Map.singleton x 1
  TyFun _ a b      -> Map.unionWith (+) (fvTypeBag a) (fvTypeBag b)
  TyApp _ a b      -> Map.unionWith (+) (fvTypeBag a) (fvTypeBag b)
  TyLam _ x _ b    -> Map.delete x (fvTypeBag b)
  TyForall _ x _ b -> Map.delete x (fvTypeBag b)
  TyBuiltin{}      -> Map.empty
  TyIFix _ a b     -> Map.unionWith (+) (fvTypeBag a) (fvTypeBag b)

-- | Freshen a TyName so that it does not equal any of the names in the set.
freshenTyName :: Set TyName -> TyName -> TyName
freshenTyName fvs (TyName (Name x j)) = TyName (Name x i)
  where i  = succ $ Set.findMax is
        is = Set.insert j $ Set.insert (toEnum 0) $ Set.mapMonotonic (_nameUnique . unTyName) fvs

-- | Get the names and types of the constructors of a datatype.
constrTypes :: Datatype TyName Name DefaultUni () -> [(Name, Type TyName DefaultUni ())]
constrTypes (Datatype _ _ xs _ cs) = [ (c, mkIterTyForall xs ty) | VarDecl _ c ty <- cs ]

-- | Get the name and type of the match function for a given datatype.
matchType :: Datatype TyName Name DefaultUni () -> (Name, Type TyName DefaultUni ())
matchType d@(Datatype _ (TyVarDecl _ a _) xs m cs) = (m, mkDestructorTy (mkScottTy () d out) d)
  where
    fvs = Set.fromList (a : [x | TyVarDecl _ x _ <- xs]) <>
          mconcat [setOf ftvTy ty | VarDecl _ _ ty <- cs]
    outName = "out_" <> _nameText (unTyName a)
    out = freshenTyName fvs $ TyName $ Name outName (toEnum 0)

-- | Bind a datatype declaration in a generator.
bindDat :: Datatype TyName Name DefaultUni ()
        -> GenTm a
        -> GenTm a
bindDat dat@(Datatype _ (TyVarDecl _ a k) _ _ _) cont =
  bindTyName a k $
  local (\ e -> e { geDatas = Map.insert a dat (geDatas e) }) $
  foldr (uncurry bindTmName) cont (matchType dat : constrTypes dat)

-- | Bind a binding.
bindBind :: Binding TyName Name DefaultUni DefaultFun ()
         -> GenTm a
         -> GenTm a
bindBind (DatatypeBind _ dat)              = bindDat dat
bindBind (TermBind _ _ (VarDecl _ x ty) _) = bindTmName x ty
-- TODO: We should generate type bindings
bindBind _                                 = error "unreachable"

-- | Bind multiple bindings
bindBinds :: Foldable f => f (Binding TyName Name DefaultUni DefaultFun ()) -> GenTm a -> GenTm a
bindBinds = flip (foldr bindBind)
