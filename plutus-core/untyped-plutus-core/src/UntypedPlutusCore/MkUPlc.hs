-- editorconfig-checker-disable-file
module UntypedPlutusCore.MkUPlc (UVarDecl (..), uvarDeclName, uvarDeclAnn, mkVar, mkIterLamAbs, Def (..), UTermDef) where

import PlutusCore.MkPlc (Def (..))
import UntypedPlutusCore.Core.Type

-- | A term definition as a variable.
type UTermDef name uni fun ann = Def (UVarDecl name ann) (Term name uni fun ann)

-- | Make a 'Var' referencing the given 'VarDecl'.
mkVar :: ann -> UVarDecl name ann -> Term name uni fun ann
mkVar ann = Var ann . _uvarDeclName

-- | Lambda abstract a list of names.
mkIterLamAbs
  :: [UVarDecl name ann]
  -> Term name uni fun ann
  -> Term name uni fun ann
mkIterLamAbs args body =
  foldr (\(UVarDecl ann name) acc -> LamAbs ann name acc) body args
