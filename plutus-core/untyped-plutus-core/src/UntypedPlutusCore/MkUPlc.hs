-- editorconfig-checker-disable-file
module UntypedPlutusCore.MkUPlc (UVarDecl (..), uvarDeclName, uvarDeclAnn, mkVar, mkIterLamAbs, Def (..), UTermDef) where

import PlutusCore.MkPlc (Def (..))
import UntypedPlutusCore.Core.Type

-- | A term definition as a variable.
type UTermDef name uni fun pat ann = Def (UVarDecl name ann) (Term name uni fun pat ann)

{-| Make a 'Var' referencing the given 'UVarDecl'.
The @ann@ is propagated from the 'UVarDecl' to the 'Var'. -}
mkVar :: UVarDecl name ann -> Term name uni fun pat ann
mkVar uvd = Var (_uvarDeclAnn uvd) (_uvarDeclName uvd)

-- | Lambda abstract a list of names.
mkIterLamAbs
  :: [UVarDecl name ann]
  -> Term name uni fun pat ann
  -> Term name uni fun pat ann
mkIterLamAbs args body =
  foldr (\(UVarDecl ann name) acc -> LamAbs ann name acc) body args
