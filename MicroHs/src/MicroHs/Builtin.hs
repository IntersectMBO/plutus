module MicroHs.Builtin(
  builtinMdl,
  builtinMdlQ,
  mkBuiltin,
  mkBuiltinQ,
  ) where
import MHSPrelude
import MicroHs.Ident
import Prelude qualified ()

-- The compiler needs a number of identifiers from libraries.
-- These are make available by (programatically) adding
--  'import Mhs.Builtin qualified as B@"
-- The name 'B@' is not a valid identifier, so these name
-- cannot be used accidentally in user code.
builtinMdl :: Ident
builtinMdl = mkIdent "B@"
builtinMdlQ :: Ident
builtinMdlQ = mkIdent "Mhs.Builtin"

-- Identifier for a builtin that will be renamed.
mkBuiltin :: SLoc -> String -> Ident
mkBuiltin loc name = qualIdent builtinMdl (mkIdentSLoc loc name)

-- Identifier for a builtin that is alread renamed.
mkBuiltinQ :: SLoc -> String -> Ident
mkBuiltinQ loc name = qualIdent builtinMdlQ (mkIdentSLoc loc name)
