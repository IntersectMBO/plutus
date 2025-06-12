module MicroHs.SymTab(
  Entry(..), entryType,
  SymTab,
  stEmpty,
  stLookup,
  stFromList,
  stInsertGlbU,
  stInsertGlbQ,
  stInsertGlbA,
  stElemsLcl,
  stKeysLcl,
  stKeysGlbU,
  stInsertLcl,
  mapMSymTab,
  ) where
import MHSPrelude
import Prelude qualified ()
--import Data.Char
import Control.Applicative
import Data.List
import GHC.Stack
import MicroHs.Builtin (builtinMdl)
import MicroHs.Expr (EType, Expr (..), conIdent)
import MicroHs.Ident (Ident, isUpperX, mkIdentSLoc, showIdent, slocIdent, unIdent)
import MicroHs.IdentMap qualified as M
import MicroHs.List

-- Symbol table
--

-- Symbol table entry for symbol i.
data Entry = Entry
  Expr             -- convert (EVar i) to this expression; sometimes just (EVar i)
  EType            -- type/kind of identifier
--  deriving(Show)

instance Show Entry where
  showsPrec _ (Entry e t) = shows e . showString " :: " . shows t

instance Eq Entry where
  Entry x _ == Entry y _  =  getIdent x == getIdent y

instance NFData Entry where
  rnf (Entry a b) = rnf a `seq` rnf b

getIdent :: Expr -> Ident
getIdent ae =
  case ae of
    EVar i   -> i
    ECon c   -> conIdent c
    EApp f _ -> getIdent f
    _        -> error "getIdent"

entryType :: Entry -> EType
entryType (Entry _ t) = t

-----------------------------------------------

-- The symbol table is split into 3 parts
--  * locals        there is usually only a few of these,
--                  so linear search is faster than a tree map
--  * unqualified   most identifiers are used unqualified, so
--        globals   it's better not to keep a globals in one table
--  * qualified     as a last resort, look among the qualified globals
--      globals
data SymTab = SymTab {
  _lcl  :: [(Ident, Entry)],     -- locals
  _uglb :: M.Map [Entry],        -- unqualified globals
  _qglb :: M.Map [Entry]         -- qualified globals
  }
--  deriving(Show)

instance Show SymTab where
  show (SymTab l ug qg) = unlines $
    ("Locals:"  : map (("  " ++) . show) l) ++
    ("UGlobals:" : map (("  " ++) . show) (M.toList ug)) ++
    ("QGlobals:" : map (("  " ++) . show) (M.toList qg))

mapMSymTab :: forall m . Monad m => (Entry -> m Entry) -> SymTab -> m SymTab
mapMSymTab f (SymTab l ug qg) = do
  l' <- mapM (\ (i, a) -> f a >>= \ a' -> return (i, a')) l
  ug' <- M.mapM (mapM f) ug
  qg' <- M.mapM (mapM f) qg
  return $ SymTab l' ug' qg'

stEmpty :: SymTab
stEmpty = SymTab [] M.empty M.empty

stLookup :: String -> Ident -> SymTab -> Either String Entry
stLookup msg i (SymTab l ug qg) =
  case lookup i l of
    Just e -> Right e
    Nothing ->
      case M.lookup i ug <|> M.lookup i qg <|> M.lookup (hackBuiltin i) ug of
        Just [e] -> Right e
        Just es  -> Left $ "ambiguous " ++ msg ++ ": " ++ showIdent i ++ " " ++
                           showListS showIdent [ getIdent e | Entry e _ <- es ]
        Nothing  -> Left $ "undefined " ++ msg ++ ": " ++ showIdent i
                           -- ++ "\n" ++ show lenv ++ "\n" ++ show genv

-- When a module uses 'import quakified Prelude()' the Mhs.Builtin (aka B@) will
-- also not be imported.  So as a last recourse, look for the identifier
-- unqualified.
hackBuiltin :: Ident -> Ident
hackBuiltin i =
  case stripPrefix (unIdent builtinMdl) (unIdent i) of
    Just ('.':s) -> mkIdentSLoc (slocIdent i) s
    _            -> i

stFromList :: [(Ident, [Entry])] -> [(Ident, [Entry])] -> SymTab
stFromList us qs = SymTab [] (M.fromListWith union us) (M.fromListWith union qs)

stElemsLcl :: SymTab -> [Entry]
stElemsLcl (SymTab l _ _) = map snd l

stKeysLcl :: SymTab -> [Ident]
stKeysLcl (SymTab l _ _) = map fst l

stKeysGlbU :: SymTab -> [Ident]
stKeysGlbU (SymTab _ m _) = M.keys m

stInsertLcl :: HasCallStack => Ident -> Entry -> SymTab -> SymTab
stInsertLcl i a (SymTab l ug qg)
{-  | isQual i = error $ "stInsertLcl " ++ showIdent i
  | otherwise -} = SymTab ((i, a) : l) ug qg

stInsertGlbU :: HasCallStack => Ident -> [Entry] -> SymTab -> SymTab
stInsertGlbU i as (SymTab l ug qg)
{-  | isQual i = error $ "stInsertGlbU " ++ showIdent i
  | otherwise -} = SymTab l (M.insert i as ug) qg

stInsertGlbQ :: HasCallStack => Ident -> [Entry] -> SymTab -> SymTab
stInsertGlbQ i as (SymTab l ug qg)
{-  | not (isQual i) = error $ "stInsertGlbQ " ++ showIdent i
  | otherwise -} = SymTab l ug (M.insert i as qg)

-- Pick the correct table to insert in
stInsertGlbA :: HasCallStack => Ident -> [Entry] -> SymTab -> SymTab
stInsertGlbA i as (SymTab l ug qg) | isQual i  = SymTab l ug (M.insertWith union i as qg)
                                   | otherwise = SymTab l (M.insertWith union i as ug) qg

isQual :: Ident -> Bool
isQual i = isUpperX (head s) && elem '.' s
  where s = unIdent i
