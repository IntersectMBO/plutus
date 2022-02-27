module UntypedPlutusCore.MkUPlc (UVarDecl (..), uvarDeclName, uvarDeclAnn, mkVar, mkIterApp, mkIterLamAbs, Def(..), UTermDef) where

import Data.List
import PlutusCore.MkPlc (Def (..))
import UntypedPlutusCore.Core.Type

-- | A term definition as a variable.
type UTermDef name uni fun ann = Def (UVarDecl name ann) (Term name uni fun ann)

-- | Make a 'Var' referencing the given 'VarDecl'.
mkVar :: ann -> UVarDecl name ann -> Term name uni fun ann
mkVar ann = Var ann . _uvarDeclName

-- | Make an iterated application.
mkIterApp
    :: ann
    -> Term name uni fun ann -- ^ @f@
    -> [Term name uni fun ann] -- ^@[ x0 ... xn ]@
    -> Term name uni fun ann -- ^ @[f x0 ... xn ]@
mkIterApp ann = foldl' (Apply ann)

-- | Lambda abstract a list of names.
mkIterLamAbs
    :: [UVarDecl name ann]
    -> Term name uni fun ann
    -> Term name uni fun ann
mkIterLamAbs args body =
    foldr (\(UVarDecl ann name ) acc -> LamAbs ann name acc) body args
