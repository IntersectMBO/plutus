{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Generators.QuickCheck.Utils where

import PlutusCore.Default
import PlutusCore.MkPlc hiding (error)
import PlutusCore.Name
import PlutusCore.Pretty
import PlutusIR
import PlutusIR.Compiler.Datatype
import PlutusIR.Core.Instance.Pretty.Readable
import PlutusIR.Subst

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Set.Lens (setOf)
import Data.String
import Prettyprinter
import Test.QuickCheck

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
