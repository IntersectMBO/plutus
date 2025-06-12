module MicroHs.Expr(
  IdentModule,
  EModule(..),
  ExportItem(..),
  ImportSpec(..),
  ImportItem(..),
  ImpType(..),
  EDef(..), showEDefs,
  Deriving(..), DerStrategy(..),
  Expr(..), eLam, eLamWithSLoc, eEqn, eEqns, showExpr, eqExpr,
  QForm(..),
  Listish(..),
  Lit(..), showLit,
  CType(..),
  EBind, showEBind, showEBinds,
  Eqn(..),
  EStmt(..),
  EAlts(..),
  EField(..), unEField,
  EAlt,
  ECaseArm,
  FunDep,
  EType, showEType, eqEType,
  EConstraint,
  EPat, patVars, isPConApp,
  EKind, kType, kConstraint,
  ESort, sKind,
  IdKind(..), idKindIdent,
  LHS,
  Constr(..), ConstrField, SType,
  ConTyInfo,
  Con(..), conIdent, conArity, conFields,
  tupleConstr, getTupleConstr,
  mkTupleSel,
  eAppI, eApp2, eAppI2, eApp3, eAppI3, eApps,
  lhsToType,
  subst, allBinders,
  allVarsExpr, allVarsBind, allVarsEqns, allVarsPat,
  setSLocExpr,
  errorMessage,
  Assoc(..), Fixity,
  getBindsVars,
  HasLoc(..),
  eForall, eForall', unForall,
  eDummy,
  impossible, impossibleShow,
  getArrow, getArrows,
  showExprRaw,
  mkEStr, mkExn,
  getAppM, getApp,
  TyVar, freeTyVars,
  getImplies,
  ) where
import Data.List
import Data.Maybe
import GHC.Stack
import MHSPrelude hiding ((<>))
import MicroHs.Builtin
import MicroHs.Ident
import Prelude qualified ()
import Text.PrettyPrint.HughesPJLite

type IdentModule = Ident

----------------------

data EModule = EModule IdentModule [ExportItem] [EDef]
--DEBUG  deriving (Show)

data ExportItem
  = ExpModule IdentModule
  | ExpTypeSome Ident [Ident]
  | ExpValue Ident
  | ExpDefault Ident
--DEBUG  deriving (Show)

data EDef
  = Data LHS [Constr] [Deriving]
  | Newtype LHS Constr [Deriving]
  | Type LHS EType
  | Fcn Ident [Eqn]
  | PatBind EPat Expr
  | Sign [Ident] EType
  | KindSign Ident EKind
  | Import ImportSpec
  | ForImp (Maybe String) Ident EType
  | Infix Fixity [Ident]
  | Class [EConstraint] LHS [FunDep] [EBind]  -- XXX will probable need initial forall with FD
  | Instance EConstraint [EBind]
  | Default (Maybe Ident) [EType]
  | Pattern LHS EPat (Maybe [Eqn])
  | StandDeriving DerStrategy Int EConstraint
  | DfltSign Ident EType                      -- only in class declarations
--DEBUG  deriving (Show)

instance NFData EDef where
  rnf (Data a b c)          = rnf a `seq` rnf b `seq` rnf c
  rnf (Newtype a b c)       = rnf a `seq` rnf b `seq` rnf c
  rnf (Type a b)            = rnf a `seq` rnf b
  rnf (Fcn a b)             = rnf a `seq` rnf b
  rnf (PatBind a b)         = rnf a `seq` rnf b
  rnf (Sign a b)            = rnf a `seq` rnf b
  rnf (KindSign a b)        = rnf a `seq` rnf b
  rnf (Import a)            = rnf a
  rnf (ForImp a b c)        = rnf a `seq` rnf b `seq` rnf c
  rnf (Infix a b)           = rnf a `seq` rnf b
  rnf (Class a b c d)       = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
  rnf (Instance a b)        = rnf a `seq` rnf b
  rnf (Default a b)         = rnf a `seq` rnf b
  rnf (Pattern a b c)       = rnf a `seq` rnf b `seq` rnf c
  rnf (StandDeriving a b c) = rnf a `seq` rnf b `seq` rnf c
  rnf (DfltSign a b)        = rnf a `seq` rnf b

data ImpType = ImpNormal | ImpBoot
  deriving (Eq)

instance NFData ImpType where rnf x = x `seq` ()

data ImportSpec = ImportSpec ImpType Bool Ident (Maybe Ident) (Maybe (Bool, [ImportItem]))  -- first Bool indicates 'qualified', second 'hiding'
--DEBUG  deriving (Show)

instance NFData ImportSpec where
  rnf (ImportSpec a b c d e) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e

data ImportItem
  = ImpTypeSome Ident [Ident]
  | ImpTypeAll Ident
  | ImpValue Ident
--DEBUG  deriving (Show)

instance NFData ImportItem where
  rnf (ImpTypeSome a b) = rnf a `seq` rnf b
  rnf (ImpTypeAll a)    = rnf a
  rnf (ImpValue a)      = rnf a

data Deriving = Deriving DerStrategy [(Int, EConstraint)] -- The Int is added by the type checker, it indicates how many arguments to keep
--DEBUG  deriving (Show)

instance NFData Deriving where
  rnf (Deriving a b) = rnf a `seq` rnf b

data DerStrategy
  = DerNone
  | DerStock
  | DerNewtype
  | DerAnyClass
  | DerVia EConstraint

instance NFData DerStrategy where
  rnf (DerVia a) = rnf a
  rnf _          = ()

data Expr
  = EVar Ident
  | EApp Expr Expr
  | EOper Expr [(Ident, Expr)]
  | ELam SLoc [Eqn]
  | ELit SLoc Lit
  | ECase Expr [ECaseArm]
  | ELet [EBind] Expr
  | ETuple [Expr]
  | EParen Expr
  | EListish Listish
  | EDo (Maybe Ident) [EStmt]
  | ESectL Expr Ident
  | ESectR Ident Expr
  | EIf Expr Expr Expr
  | EMultiIf EAlts
  | ESign Expr EType
  | ENegApp Expr
  | EUpdate Expr [EField]
  | ESelect [Ident]
  | ETypeArg EType           -- @type
  -- only in patterns
  | EAt Ident EPat
  | EViewPat Expr EPat
  | ELazy Bool EPat           -- True indicates ~p, False indicates !p
  | EOr [EPat]
  -- only in types
  | EForall QForm [IdKind] EType
  -- only while type checking
  | EUVar Int
  | EQVar Expr EType             -- already resolved identifier
  -- only after type checking
  | ECon Con
--DEBUG  deriving (Show)

instance NFData Expr where
  rnf (EVar a)        = rnf a
  rnf (EApp a b)      = rnf a `seq` rnf b
  rnf (EOper a b)     = rnf a `seq` rnf b
  rnf (ELam a b)      = rnf a `seq` rnf b
  rnf (ELit a b)      = rnf a `seq` rnf b
  rnf (ECase a b)     = rnf a `seq` rnf b
  rnf (ELet a b)      = rnf a `seq` rnf b
  rnf (ETuple a)      = rnf a
  rnf (EParen a)      = rnf a
  rnf (EListish a)    = rnf a
  rnf (EDo a b)       = rnf a `seq` rnf b
  rnf (ESectL a b)    = rnf a `seq` rnf b
  rnf (ESectR a b)    = rnf a `seq` rnf b
  rnf (EIf a b c)     = rnf a `seq` rnf b `seq` rnf c
  rnf (EMultiIf a)    = rnf a
  rnf (ESign a b)     = rnf a `seq` rnf b
  rnf (ENegApp a)     = rnf a
  rnf (EUpdate a b)   = rnf a `seq` rnf b
  rnf (ESelect a)     = rnf a
  rnf (ETypeArg a)    = rnf a
  rnf (EAt a b)       = rnf a `seq` rnf b
  rnf (EViewPat a b)  = rnf a `seq` rnf b
  rnf (ELazy a b)     = rnf a `seq` rnf b
  rnf (EOr a)         = rnf a
  rnf (EForall a b c) = rnf a `seq` rnf b `seq` rnf c
  rnf (EUVar a)       = rnf a
  rnf (EQVar a b)     = rnf a `seq` rnf b
  rnf (ECon a)        = rnf a

data QForm = QImpl | QExpl | QReqd

instance NFData QForm where
  rnf q = seq q ()

data EField
  = EField [Ident] Expr     -- a.b = e
  | EFieldPun [Ident]       -- a.b
  | EFieldWild              -- ..
--DEBUG  deriving (Show)

instance NFData EField where
  rnf (EField a b)  = rnf a `seq` rnf b
  rnf (EFieldPun a) = rnf a
  rnf EFieldWild    = ()

unEField :: EField -> ([Ident], Expr)
unEField (EField is e) = (is, e)
unEField _             = impossible

type FunDep = ([Ident], [Ident])

eLam :: [EPat] -> Expr -> Expr
eLam = eLamWithSLoc noSLoc

eLamWithSLoc :: SLoc -> [EPat] -> Expr -> Expr
eLamWithSLoc loc ps e = ELam loc $ eEqns ps e

eEqns :: [EPat] -> Expr -> [Eqn]
eEqns ps e = [eEqn ps e]

eEqn :: [EPat] -> Expr -> Eqn
eEqn ps e = Eqn ps (EAlts [([], e)] [])

type FieldName = Ident

data Con
  = ConData ConTyInfo Ident [FieldName]
  | ConNew Ident [FieldName]
  | ConSyn Ident Int (Expr, EType)
--DEBUG  deriving(Show)

instance NFData Con where
  rnf (ConData a b c) = rnf a `seq` rnf b `seq` rnf c
  rnf (ConNew a b)    = rnf a `seq` rnf b
  rnf (ConSyn a b c)  = rnf a `seq` rnf b `seq` rnf c

data Listish
  = LList [Expr]
  | LCompr Expr [EStmt]
  | LFrom Expr
  | LFromTo Expr Expr
  | LFromThen Expr Expr
  | LFromThenTo Expr Expr Expr
--DEBUG  deriving(Show)

instance NFData Listish where
  rnf (LList a)           = rnf a
  rnf (LCompr a b)        = rnf a `seq` rnf b
  rnf (LFrom a)           = rnf a
  rnf (LFromTo a b)       = rnf a `seq` rnf b
  rnf (LFromThen a b)     = rnf a `seq` rnf b
  rnf (LFromThenTo a b c) = rnf a `seq` rnf b `seq` rnf c

conIdent :: HasCallStack =>
            Con -> Ident
conIdent (ConData _ i _) = i
conIdent (ConNew i _)    = i
conIdent (ConSyn i _ _)  = i

conArity :: Con -> Int
conArity (ConData cs i _) = fromMaybe (error "conArity") $ lookup i cs
conArity (ConNew _ _)     = 1
conArity (ConSyn _ n _)   = n

conFields :: Con -> [FieldName]
conFields (ConData _ _ fs) = fs
conFields (ConNew _ fs)    = fs
conFields ConSyn{}         = []

instance Eq Con where
  (==) (ConData _ i _)   (ConData _ j _)   = i == j
  (==) (ConNew    i _)   (ConNew    j _)   = i == j
  (==) (ConSyn    i _ _) (ConSyn    j _ _) = i == j
  (==) _                 _                 = False

data Lit
  = LInt Int
  | LInteger Integer
  | LDouble Double
  | LRat Rational
  | LChar Char
  | LStr String
  | LBStr String            -- bytestring
  | LPrim String
  | LExn String             -- exception to raise
  | LForImp String CType
  | LTick String
--DEBUG  deriving (Show)
  deriving (Eq, Show)

instance NFData Lit where
  rnf (LInt a)      = rnf a
  rnf (LInteger a)  = rnf a
  rnf (LDouble a)   = rnf a
  rnf (LRat a)      = rnf a
  rnf (LChar a)     = rnf a
  rnf (LStr a)      = rnf a
  rnf (LBStr a)     = rnf a
  rnf (LPrim a)     = rnf a
  rnf (LExn a)      = rnf a
  rnf (LForImp a b) = rnf a `seq` rnf b
  rnf (LTick a)     = rnf a

-- A type of a C FFI function
newtype CType = CType EType deriving (Show)

instance Eq CType where
  _ == _  =  True    -- Just ignore the CType

instance NFData CType where
  rnf (CType t) = rnf t

type ECaseArm = (EPat, EAlts)

data EStmt = SBind EPat Expr | SThen Expr | SLet [EBind]
--DEBUG  deriving (Show)

instance NFData EStmt where
  rnf (SBind a b) = rnf a `seq` rnf b
  rnf (SThen a)   = rnf a
  rnf (SLet a)    = rnf a

type EBind = EDef   -- subset with Fcn, PatBind, Sign, and DfltSign

-- A single equation for a function
data Eqn = Eqn [EPat] EAlts
--DEBUG  deriving (Show)

instance NFData Eqn where
  rnf (Eqn a b) = rnf a `seq` rnf b

data EAlts = EAlts [EAlt] [EBind]
--DEBUG  deriving (Show)

instance NFData EAlts where
  rnf (EAlts a b) = rnf a `seq` rnf b

type EAlt = ([EStmt], Expr)

type ConTyInfo = [(Ident, Int)]    -- All constructors with their arities

type EPat = Expr

isPConApp :: EPat -> Bool
isPConApp (EVar i)   = isConIdent i
isPConApp (EApp f _) = isPConApp f
isPConApp (EAt _ p)  = isPConApp p
isPConApp _          = True

-- Variables bound in a pattern.
-- Could use difference lists, but it seems a little slower.
patVars :: HasCallStack => EPat -> [Ident]
patVars apat =
  case apat of
    EVar i              -> add i []
    EApp p1 p2          -> patVars p1 ++ patVars p2
    EOper p1 ips        -> patVars p1 ++ concatMap (\ (i, p2) -> i `add` patVars p2) ips
    ELit _ _            -> []
    ETuple ps           -> concatMap patVars ps
    EParen p            -> patVars p
    EListish (LList ps) -> concatMap patVars ps
    ESign p _           -> patVars p
    EAt i p             -> i `add` patVars p
    EViewPat _ p        -> patVars p
    ELazy _ p           -> patVars p
    ECon _              -> []
    EUpdate _ fs        -> concatMap field fs
    ENegApp _           -> []
    EOr ps              -> concatMap patVars ps
    _                   -> error $ "patVars " ++ showExpr apat
  where add i is | isConIdent i || isDummyIdent i = is
                 | otherwise = i : is
        field (EField _ p)   = patVars p
        field (EFieldPun is) = [last is]
        field EFieldWild     = impossible

type LHS = (Ident, [IdKind])

data Constr = Constr
  [IdKind] [EConstraint]          -- existentials: forall vs . ctx =>
  Ident                           -- constructor name
  (Either [SType] [ConstrField])  -- types or named fields
  deriving(Show)

instance NFData Constr where
  rnf (Constr a b c d) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d

type ConstrField = (Ident, SType)              -- record label and type
type SType = (Bool, EType)                     -- the Bool indicates strict

-- Expr restricted to
--  * after desugaring: EApp and EVar
--  * before desugaring: EApp, EVar, ETuple, EList
type EType = Expr

type EConstraint = EType

data IdKind = IdKind Ident EKind
--DEBUG  deriving (Show)

instance Show IdKind where
  show (IdKind i k) = "(" ++ show i ++ "::" ++ show k ++ ")"

instance NFData IdKind where
  rnf (IdKind a b) = rnf a `seq` rnf b

idKindIdent :: IdKind -> Ident
idKindIdent (IdKind i _) = i

type EKind = EType
type ESort = EType

sKind :: ESort
sKind = EVar (mkIdent "Primitives.Kind")

kType :: EKind
kType = EVar (mkIdent "Primitives.Type")

kConstraint :: EKind
kConstraint = EVar (mkIdent "Primitives.Constraint")

tupleConstr :: SLoc -> Int -> Ident
tupleConstr loc 0 = mkIdentSLoc loc "()"
tupleConstr   _ 1 = error "tupleConstr"
tupleConstr loc n = mkIdentSLoc loc (replicate (n - 1) ',')

-- Check if it is a tuple constructor
getTupleConstr :: Ident -> Maybe Int
getTupleConstr i =
  case unIdent i of
    "()"   -> Just 0
    ',':xs -> Just (length xs + 2)  -- "," is 2-tuple
    _      -> Nothing

-- Create a tuple selector, component i (0 based) of n
mkTupleSel :: Int -> Int -> Expr
mkTupleSel i n = eLam [ETuple [ EVar $ if k == i then x else dummyIdent | k <- [0 .. n - 1] ]] (EVar x)
  where x = mkIdent "$x"

eAppI :: Ident -> Expr -> Expr
eAppI i a = EApp (EVar i) a

eApp2 :: Expr -> Expr -> Expr -> Expr
eApp2 a b c = EApp (EApp a b) c

eAppI2 :: Ident -> Expr -> Expr -> Expr
eAppI2 a b c = EApp (EApp (EVar a) b) c

eApp3 :: Expr -> Expr -> Expr -> Expr -> Expr
eApp3 a b c d = EApp (eApp2 a b c) d

eAppI3 :: Ident -> Expr -> Expr -> Expr -> Expr
eAppI3 a b c d = EApp (eAppI2 a b c) d

eApps :: Expr -> [Expr] -> Expr
eApps = foldl EApp

lhsToType :: LHS -> EType
lhsToType (i, iks) = eApps (EVar i) $ map (EVar . idKindIdent) iks

---------------------------------

-- Get the location of a syntactic element
class HasLoc a where
  getSLoc :: a -> SLoc

instance HasLoc Ident where
  getSLoc = slocIdent

instance HasLoc EDef where
  getSLoc (Fcn i _)      = getSLoc i
  getSLoc (PatBind p _)  = getSLoc p
  getSLoc (Sign i _)     = getSLoc i
  getSLoc (DfltSign i _) = getSLoc i
  getSLoc (Infix _ is)   = getSLoc is
  getSLoc _              = error "HasLoc EDef: unimplemented"

-- Approximate location; only identifiers and literals carry a location
instance HasLoc Expr where
  getSLoc (EVar i)          = getSLoc i
  getSLoc (EApp e _)        = getSLoc e
  getSLoc (EOper e _)       = getSLoc e
  getSLoc (ELam l _)        = l
  getSLoc (ELit l _)        = l
  getSLoc (ECase e _)       = getSLoc e
  getSLoc (ELet bs _)       = getSLoc bs
  getSLoc (ETuple es)       = getSLoc es
  getSLoc (EParen e)        = getSLoc e
  getSLoc (EListish l)      = getSLoc l
  getSLoc (EDo (Just i) _)  = getSLoc i
  getSLoc (EDo _ ss)        = getSLoc ss
  getSLoc (ESectL e _)      = getSLoc e
  getSLoc (ESectR i _)      = getSLoc i
  getSLoc (EIf e _ _)       = getSLoc e
  getSLoc (EMultiIf e)      = getSLoc e
  getSLoc (ESign e _)       = getSLoc e
  getSLoc (ENegApp e)       = getSLoc e
  getSLoc (EUpdate e _)     = getSLoc e
  getSLoc (ESelect is)      = getSLoc is
  getSLoc (ETypeArg t)      = getSLoc t
  getSLoc (EAt i _)         = getSLoc i
  getSLoc (EViewPat e _)    = getSLoc e
  getSLoc (ELazy _ e)       = getSLoc e
  getSLoc (EOr es)          = getSLoc es
  getSLoc (EUVar _)         = noSLoc -- error "getSLoc EUVar"
  getSLoc (EQVar e _)       = getSLoc e
  getSLoc (ECon c)          = getSLoc c
  getSLoc (EForall _ [] e)  = getSLoc e
  getSLoc (EForall _ iks _) = getSLoc iks

instance HasLoc a => HasLoc [a] where
  getSLoc []    = noSLoc  -- XXX shouldn't happen
  getSLoc (a:_) = getSLoc a

instance HasLoc IdKind where
  getSLoc (IdKind i _) = getSLoc i

instance HasLoc Con where
  getSLoc (ConData _ i _) = getSLoc i
  getSLoc (ConNew i _)    = getSLoc i
  getSLoc (ConSyn i _ _)  = getSLoc i

instance HasLoc Listish where
  getSLoc (LList es)          = getSLoc es
  getSLoc (LCompr e _)        = getSLoc e
  getSLoc (LFrom e)           = getSLoc e
  getSLoc (LFromTo e _)       = getSLoc e
  getSLoc (LFromThen e _)     = getSLoc e
  getSLoc (LFromThenTo e _ _) = getSLoc e

instance HasLoc EStmt where
  getSLoc (SBind p _) = getSLoc p
  getSLoc (SThen e)   = getSLoc e
  getSLoc (SLet bs)   = getSLoc bs

instance HasLoc Eqn where
  getSLoc (Eqn [] a)    = getSLoc a
  getSLoc (Eqn (p:_) _) = getSLoc p

instance HasLoc EAlts where
  getSLoc (EAlts as _) = getSLoc as

instance HasLoc a => HasLoc (a, b) where
  getSLoc (a, _) = getSLoc a

---------------------------------

data Assoc = AssocLeft | AssocRight | AssocNone
--DEBUG  deriving (Show)
  deriving (Eq)

type Fixity = (Assoc, Int)

instance NFData Assoc where rnf x = x `seq` ()

---------------------------------

-- Enough to handle subsitution in (undesguared) types
subst :: [(Ident, Expr)] -> Expr -> Expr
subst [] = id
subst s =
  let
    sub ae =
      case ae of
        EVar i -> fromMaybe ae $ lookup i s
        EApp f a -> EApp (sub f) (sub a)
        ESign e t -> ESign (sub e) t
        EUVar _ -> ae
        EForall b iks t | null (vs `intersect` is) -> EForall b iks $ subst s' t
                        | otherwise ->
                          -- We need to alpha convert to avoid accidental capture
                          let used = freeTyVars [t]
                              new = allBinders \\ (is ++ vs ++ used)
                              iks'  = zipWith (\ (IdKind _ k) n -> IdKind n k) iks new
                              alpha = zipWith (\ (IdKind i _) n -> (i, EVar n)) iks new
                          in  subst s' $ EForall b iks' $ subst alpha t
          where is = map idKindIdent iks
                s' = [ x | x@(i, _) <- s, i `notElem` is ]
                vs = freeTyVars (map snd s')    -- these are free in s'

        ELit _ _ -> ae
        ETuple ts -> ETuple (map sub ts)
        EOper t1 its -> EOper (sub t1) (map (second sub) its)
        EListish (LList [t]) -> EListish (LList [sub t])
        EParen t -> EParen (sub t)
        _ -> error $ "subst unimplemented " ++  show ae
  in sub

allBinders :: [Ident] -- a,b,...,z,a1,a2,...
allBinders = [ mkIdent [x] | x <- ['a' .. 'z'] ] ++
             [ mkIdent ('a' : show i) | i <- [1::Int ..]]

---------------------------------

-- XXX needs more?
eqEType :: EType -> EType -> Bool
eqEType = eqExpr

-- Very partial implementation of Expr equality.
-- It is only used to compare instances, so this suffices.
eqExpr :: HasCallStack =>
          Expr -> Expr -> Bool
eqExpr (EVar i) (EVar i')      = i == i'
eqExpr (ELit _ l) (ELit _ l')  = l == l'
eqExpr (EApp f a) (EApp f' a') = eqExpr f f' && eqExpr a a'
eqExpr (EUVar r) (EUVar r')    = r == r'
eqExpr _ _                     = False -- XXX good enough for instances
--eqExpr e1 e2 = error $ "eqExpr: unimplemented " ++ showExpr e1 ++ " == " ++ showExpr e2

---------------------------------

type DList a = [a] -> [a]

composeMap :: forall a b . (a -> DList b) -> [a] -> DList b
composeMap _ []     = id
composeMap f (x:xs) = f x . composeMap f xs

allVarsBind :: EBind -> [Ident]
allVarsBind b = allVarsBind' b []

allVarsBind' :: EBind -> DList Ident
allVarsBind' abind =
  case abind of
    Fcn i eqns   -> (i:) . composeMap allVarsEqn eqns
    PatBind p e  -> allVarsPat p . allVarsExpr' e
    Sign is _    -> (is ++)
    DfltSign i _ -> (i:)
    Infix _ _    -> id
    _            -> impossible

allVarsEqns :: [Eqn] -> [Ident]
allVarsEqns eqns = composeMap allVarsEqn eqns []

allVarsEqn :: Eqn -> DList Ident
allVarsEqn eqn =
  case eqn of
    Eqn ps alts -> composeMap allVarsPat ps . allVarsAlts alts

allVarsAlts :: EAlts -> DList Ident
allVarsAlts (EAlts alts bs) = composeMap allVarsAlt alts . composeMap allVarsBind' bs

allVarsAlt :: EAlt -> DList Ident
allVarsAlt (ss, e) = composeMap allVarsStmt ss . allVarsExpr' e

allVarsPat :: EPat -> DList Ident
allVarsPat = allVarsExpr'

allVarsExpr :: Expr -> [Ident]
allVarsExpr e = allVarsExpr' e []

allVarsExpr' :: Expr -> DList Ident
allVarsExpr' aexpr =
  case aexpr of
    EVar i              -> (i:)
    EApp e1 e2          -> allVarsExpr' e1 . allVarsExpr' e2
    EOper e1 ies        -> allVarsExpr' e1 . composeMap (\ (i,e2) -> (i :) . allVarsExpr' e2) ies
    ELam _ qs           -> composeMap allVarsEqn qs
    ELit _ _            -> id
    ECase e as          -> allVarsExpr' e . composeMap allVarsCaseArm as
    ELet bs e           -> composeMap allVarsBind' bs . allVarsExpr' e
    ETuple es           -> composeMap allVarsExpr' es
    EParen e            -> allVarsExpr' e
    EListish (LList es) -> composeMap allVarsExpr' es
    EDo mi ss           -> maybe id (:) mi . composeMap allVarsStmt ss
    ESectL e i          -> (i :) . allVarsExpr' e
    ESectR i e          -> (i :) . allVarsExpr' e
    EIf e1 e2 e3        -> allVarsExpr' e1 . allVarsExpr' e2 . allVarsExpr' e3
    EMultiIf e          -> allVarsAlts e
    EListish l          -> allVarsListish l
    ESign e _           -> allVarsExpr' e
    ENegApp e           -> allVarsExpr' e
    EUpdate e ies       -> allVarsExpr' e . composeMap field ies
    ESelect _           -> id
    ETypeArg _          -> id
    EAt i e             -> (i :) . allVarsExpr' e
    EViewPat e p        -> allVarsExpr' e . allVarsExpr' p
    ELazy _ p           -> allVarsExpr' p
    EOr ps              -> composeMap allVarsExpr' ps
    EUVar _             -> id
    EQVar e _           -> allVarsExpr' e
    ECon c              -> (conIdent c :)
    EForall _ iks e     -> (map (\ (IdKind i _) -> i) iks ++) . allVarsExpr' e
  where field (EField _ e)   = allVarsExpr' e
        field (EFieldPun is) = (last is :)
        field EFieldWild     = impossible

allVarsListish :: Listish -> DList Ident
allVarsListish (LList es)             = composeMap allVarsExpr' es
allVarsListish (LCompr e ss)          = allVarsExpr' e . composeMap allVarsStmt ss
allVarsListish (LFrom e)              = allVarsExpr' e
allVarsListish (LFromTo e1 e2)        = allVarsExpr' e1 . allVarsExpr' e2
allVarsListish (LFromThen e1 e2)      = allVarsExpr' e1 . allVarsExpr' e2
allVarsListish (LFromThenTo e1 e2 e3) = allVarsExpr' e1 . allVarsExpr' e2 . allVarsExpr' e3

allVarsCaseArm :: ECaseArm -> DList Ident
allVarsCaseArm (p, alts) = allVarsPat p . allVarsAlts alts

allVarsStmt :: EStmt -> DList Ident
allVarsStmt astmt =
  case astmt of
    SBind p e -> allVarsPat p . allVarsExpr' e
    SThen e   -> allVarsExpr' e
    SLet bs   -> composeMap allVarsBind' bs

-----------------------------

setSLocExpr :: SLoc -> Expr -> Expr
setSLocExpr l (EVar i)   = EVar (setSLocIdent l i)
setSLocExpr l (ECon c)   = ECon (setSLocCon l c)
setSLocExpr l (ELit _ k) = ELit l k
setSLocExpr _ _          = error "setSLocExpr"  -- what other cases do we need?

setSLocCon :: SLoc -> Con -> Con
setSLocCon l (ConData ti i fs) = ConData ti (setSLocIdent l i) fs
setSLocCon l (ConNew i fs)     = ConNew (setSLocIdent l i) fs
setSLocCon l (ConSyn i n m)    = ConSyn (setSLocIdent l i) n m

errorMessage :: forall a .
                HasCallStack =>
                SLoc -> String -> a
errorMessage loc msg = error $ showSLoc loc ++ ": " ++ msg

----------------

instance Show EModule where
  show (EModule nm _ ds) = "module " ++ showIdent nm ++ "(...) where\n" ++ showEDefs ds

instance Show Expr where
  show = showExpr

instance Show Eqn where
  show eqn = render $ ppEqns (text "_") (text "=") [eqn]

instance Show EDef where
  show d = showEDefs [d]

showExpr :: Expr -> String
showExpr = render . ppExpr

showExprRaw :: Expr -> String
showExprRaw = render . ppExprRaw

showEDefs :: [EDef] -> String
showEDefs = render . ppEDefs

showEBind :: EBind -> String
showEBind = render . ppEBind

showEBinds :: [EBind] -> String
showEBinds = render . vcat . map ppEBind

showEType :: EType -> String
showEType = render . ppEType

ppImportItem :: ImportItem -> Doc
ppImportItem ae =
  case ae of
    ImpTypeSome i [] -> ppIdent i
    ImpTypeSome i is -> ppIdent i <> parens (ppCommaSep $ map ppIdent is)
    ImpTypeAll i     -> ppIdent i <> text "(..)"
    ImpValue i       -> ppIdent i

ppCommaSep :: [Doc] -> Doc
ppCommaSep = hsep . punctuate (text ",")

ppEBind :: EBind -> Doc
ppEBind = ppEDef

ppEDef :: EDef -> Doc
ppEDef def =
  case def of
    Data lhs [] ds -> text "data" <+> ppLHS lhs <+> ppDerivings ds
    Data lhs cs ds -> text "data" <+> ppLHS lhs <+> text "=" <+> hsep (punctuate (text " |") (map ppConstr cs)) <+> ppDerivings ds
    Newtype lhs c ds -> text "newtype" <+> ppLHS lhs <+> text "=" <+> ppConstr c <+> ppDerivings ds
    Type lhs t -> text "type" <+> ppLHS lhs <+> text "=" <+> ppEType t
    Fcn i eqns -> ppEqns (ppIdent i) (text "=") eqns
    PatBind p e -> ppEPat p <+> text "=" <+> ppExpr e
    Sign is t -> hsep (punctuate (text ",") (map ppIdent is)) <+> text "::" <+> ppEType t
    KindSign i t -> text "type" <+> ppIdent i <+> text "::" <+> ppEKind t
    Import (ImportSpec b q m mm mis) -> text "import" <+>
      (if b == ImpBoot then text "{-# SOURCE #-}" else empty) <+>
      (if q then text "qualified" else empty) <+> ppIdent m <> text (maybe "" ((" as " ++) . unIdent) mm) <>
      case mis of
        Nothing -> empty
        Just (h, is) -> text (if h then " hiding" else "") <> parens (hsep $ punctuate (text ",") (map ppImportItem is))
    ForImp ie i t -> text "foreign import ccall" <+> maybe empty (text . show) ie <+> ppIdent i <+> text "::" <+> ppEType t
    Infix (a, p) is -> text ("infix" ++ f a) <+> text (show p) <+> hsep (punctuate (text ", ") (map ppIdent is))
      where f AssocLeft = "l"; f AssocRight = "r"; f AssocNone = ""
    Class sup lhs fds bs -> ppWhere (text "class" <+> ppCtx sup <+> ppLHS lhs <+> ppFunDeps fds) bs
    Instance ct bs -> ppWhere (text "instance" <+> ppEType ct) bs
    Default mc ts -> text "default" <+> maybe empty ppIdent mc <+> parens (hsep (punctuate (text ", ") (map ppEType ts)))
    Pattern lhs@(i,_) p meqns -> text "pattern" <+> ppLHS lhs <+> text "=" <+> ppExpr p <+> maybe empty (ppWhere (text ";") . (:[]) . Fcn i) meqns
    StandDeriving _s _narg ct -> text "deriving instance" <+> ppEType ct
    DfltSign i t -> text "default" <+> ppIdent i <+> text "::" <+> ppEType t

ppDerivings :: [Deriving] -> Doc
ppDerivings = sep . map ppDeriving

ppDeriving :: Deriving -> Doc
ppDeriving (Deriving s ds) = text "deriving" <+>
  case s of
    DerNone     -> empty
    DerStock    -> text "stock"
    DerNewtype  -> text "newtype"
    DerAnyClass -> text "anyclass"
    DerVia _    -> empty
  <+> parens (hsep $ punctuate (text ",") (map (ppExpr . snd) ds))
  <+>
  case s of
    DerVia t -> text "via" <+> ppEType t
    _        -> empty

ppCtx :: [EConstraint] -> Doc
ppCtx [] = empty
ppCtx ts = ppEType (ETuple ts) <+> text "=>"

ppFunDeps :: [FunDep] -> Doc
ppFunDeps [] = empty
ppFunDeps fds =
  text "|" <+> hsep (punctuate (text ",") (map (\ (is, os) -> hsep (map ppIdent is) <+> text "-" <+> hsep (map ppIdent os)) fds))

ppEqns :: Doc -> Doc -> [Eqn] -> Doc
ppEqns name sepr = vcat . map (\ (Eqn ps alts) -> sep [name <+> hsep (map ppEPat ps), ppAlts sepr alts])

ppConstr :: Constr -> Doc
ppConstr (Constr iks ct c cs) = ppForall QImpl iks <+> ppCtx ct <+> ppIdent c <+> ppCs cs
  where ppCs (Left  ts) = hsep (map ppSType ts)
        ppCs (Right fs) = braces (hsep $ map f fs)
          where f (i, t) = ppIdent i <+> text "::" <+> ppSType t <> text ","

ppSType :: SType -> Doc
ppSType (False, t) = ppEType t
ppSType (True, t)  = text "!" <> ppEType t

ppLHS :: LHS -> Doc
ppLHS (f, vs) = hsep (ppIdent f : map ppIdKind vs)

ppIdKind :: IdKind -> Doc
ppIdKind (IdKind i (EVar d)) | isDummyIdent d = ppIdent i
ppIdKind (IdKind i k) = parens $ ppIdent i <> text "::" <> ppEKind k

ppEDefs :: [EDef] -> Doc
ppEDefs ds = vcat (map pp ds)
  where pp d@(Sign _ _) = ppEDef d
        pp d@(Import _) = ppEDef d
        pp d            = ppEDef d $+$ text ""

ppAlts :: Doc -> EAlts -> Doc
ppAlts asep (EAlts alts bs) = ppWhere (ppAltsL asep alts) bs

ppWhere :: Doc -> [EBind] -> Doc
ppWhere d [] = d
ppWhere d bs = (d <+> text "where") $+$ nest 2 (vcat (map ppEBind bs))

ppAltsL :: Doc -> [EAlt] -> Doc
ppAltsL asep [([], e)] = text "" <+> asep <+> ppExpr e
ppAltsL asep alts      = vcat (map (ppAlt asep) alts)

ppAlt :: Doc -> EAlt -> Doc
ppAlt asep (ss, e) = text " |" <+> hsep (punctuate (text ",") (map ppEStmt ss)) <+> asep <+> ppExpr e

ppExprRaw :: Expr -> Doc
ppExprRaw = ppExprR True

ppExpr :: Expr -> Doc
ppExpr = ppExprR False

ppExprR :: Bool -> Expr -> Doc
ppExprR raw = ppE
  where
    ppE :: Expr -> Doc
    ppE ae =
      case ae of
        EVar i | raw            -> text si
               | isOperChar cop -> parens (text op)
               | otherwise      -> text s
                 where op = unIdent (unQualIdent i)
                       si = unIdent i
                       s = if "inst$" `isInfixOf` si then si else op
                       cop = head op
        EApp _ _ -> ppApp [] ae
        EOper e ies -> ppE (foldl (\ e1 (i, e2) -> EApp (EApp (EVar i) e1) e2) e ies)
        ELam _ qs -> parens $ text "\\" <> ppEqns empty (text "->") qs
        ELit _ i -> text (showLit i)
        ECase e as -> text "case" <+> ppE e <+> text "of" $$ nest 2 (vcat (map ppCaseArm as))
        ELet bs e -> text "let" $$ nest 2 (vcat (map ppEBind bs)) $$ text "in" <+> ppE e
        ETuple es -> parens $ hsep $ punctuate (text ",") (map ppE es)
        EParen e -> parens (ppE e)
        EDo mn ss -> maybe (text "do") (\ n -> ppIdent n <> text ".do") mn $$ nest 2 (vcat (map ppEStmt ss))
        ESectL e i -> parens $ ppE e <+> ppIdent i
        ESectR i e -> parens $ ppIdent i <+> ppE e
        EIf e1 e2 e3 -> parens $ sep [text "if" <+> ppE e1, text "then" <+> ppE e2, text "else" <+> ppE e3]
        EMultiIf e -> text "if" <+> ppAlts (text "->") e
        EListish l -> ppListish l
        ESign e t -> parens $ ppE e <+> text "::" <+> ppEType t
        ENegApp e -> text "-" <+> ppE e
        EUpdate ee ies -> ppE ee <> text "{" <+> hsep (punctuate (text ",") (map ppField ies)) <+> text "}"
        ESelect is -> parens $ hcat $ map (\ i -> text "." <> ppIdent i) is
        ETypeArg t -> text "@" <> ppE t
        EAt i e -> ppIdent i <> text "@" <> ppE e
        EViewPat e p -> parens $ ppE e <+> text "->" <+> ppE p
        ELazy True p -> text "~" <> ppE p
        ELazy False p -> text "!" <> ppE p
        EOr ps -> parens $ hsep (punctuate (text ";") (map ppE ps))
        EUVar i -> text ("_a" ++ show i)
        EQVar e t -> parens $ ppE e <> text ":::" <> ppE t
        ECon c -> {-text "***" <>-} ppCon c
        EForall q iks e -> parens $ ppForall q iks <+> ppEType e

    ppApp :: [Expr] -> Expr -> Doc
    ppApp as (EApp f a) = ppApp (a:as) f
    ppApp as f | raw = ppApply f as
    ppApp as (EVar i) | isOperChar cop, [a, b] <- as = parens $ ppE a <+> text op <+> ppExpr b
                      | isOperChar cop, [a] <- as    = parens $ ppE a <+> text op
                      | cop == ',' && length op + 1 == length as
                                                     = ppE (ETuple as)
                      | op == "[]", length as == 1   = ppE (EListish (LList as))
                        where op = unIdent (unQualIdent i)
                              cop = head op
    ppApp as f = ppApply f as
    ppApply f as = parens $ hsep (map ppE (f:as))

ppField :: EField -> Doc
ppField (EField is e)  = hcat (punctuate (text ".") (map ppIdent is)) <+> text "=" <+> ppExpr e
ppField (EFieldPun is) = hcat (punctuate (text ".") (map ppIdent is))
ppField EFieldWild     = text ".."

ppForall :: QForm -> [IdKind] -> Doc
--ppForall [] = empty
ppForall q iks = text "forall" <+> hsep (map ppIdKind iks) <+> text qs
  where qs = case q of QReqd -> "->"; _ -> "."

ppListish :: Listish -> Doc
ppListish (LList es) = ppList ppExpr es
ppListish (LCompr e ss) = brackets $ ppExpr e <+> text "|" <+> hsep (punctuate (text ",") (map ppEStmt ss))
ppListish (LFrom e1) = brackets $ ppExpr e1 <> text ".."
ppListish (LFromTo e1 e2) = brackets $ ppExpr e1 <> text ".." <> ppExpr e2
ppListish (LFromThen e1 e2) = brackets $ ppExpr e1 <> text "," <> ppExpr e2 <> text ".."
ppListish (LFromThenTo e1 e2 e3) = brackets $ ppExpr e1 <> text "," <> ppExpr e2 <> text ".." <> ppExpr e3

ppCon :: Con -> Doc
ppCon (ConData _ s _) = ppIdent s
ppCon (ConNew s _)    = ppIdent s
ppCon (ConSyn s _ _)  = ppIdent s

-- Literals are tagged the way they appear in the combinator file:
--  #   Int
--  %   Double
--  '   Char    (not in file)
--  "   String
--  ^   FFI function
--      primitive
showLit :: Lit -> String
showLit l =
  case l of
    LInt i      -> '#' : show i
    LInteger i  -> '#' : '#' : show i
    LDouble d   -> '&' : show d
    LRat r      -> '%' : show r
    LChar c     -> show c
    LStr s      -> show s
    LBStr s     -> show s
    LPrim s     -> s
    LExn s      -> s
    LForImp s _-> '^' : last (words s)  -- XXX needs improvement
    LTick s     -> '!' : s

ppEStmt :: EStmt -> Doc
ppEStmt as =
  case as of
    SBind p e -> ppEPat p <+> text "<-" <+> ppExpr e
    SThen e   -> ppExpr e
    SLet bs   -> text "let" $$ nest 2 (vcat (map ppEBind bs))

ppCaseArm :: ECaseArm -> Doc
ppCaseArm arm =
  case arm of
    (p, alts) -> ppEPat p <> ppAlts (text "->") alts

ppEPat :: EPat -> Doc
ppEPat = ppExpr

ppEType :: EType -> Doc
ppEType = ppExpr

ppEKind :: EKind -> Doc
ppEKind = ppEType

ppList :: forall a . (a -> Doc) -> [a] -> Doc
ppList pp xs = brackets $ hsep $ punctuate (text ",") (map pp xs)

getBindVars :: HasCallStack => EBind -> [Ident]
getBindVars abind =
  case abind of
    Fcn i _     -> [i]
    PatBind p _ -> patVars p
    _           -> []

getBindsVars :: HasCallStack => [EBind] -> [Ident]
getBindsVars = concatMap getBindVars

eForall :: [IdKind] -> EType -> EType
eForall = eForall' QExpl

eForall' :: QForm -> [IdKind] -> EType -> EType
eForall' _ [] t = t
eForall' b vs t = EForall b vs t

unForall :: EType -> ([IdKind], EType)
unForall (EForall _ xs t) = (xs, t)
unForall               t  = ([], t)

eDummy :: Expr
eDummy = EVar dummyIdent

impossible :: forall a .
              HasCallStack =>
              a
impossible = error "impossible"

impossibleShow :: forall a b .
                  (HasCallStack, Show a, HasLoc a) => a -> b
impossibleShow a = error $ "impossible: " ++ show (getSLoc a) ++ " " ++ show a

-----------

-- Probably belongs somewhere else
getArrow :: EType -> Maybe (EType, EType)
getArrow (EApp (EApp (EVar n) a) b) =
  if isIdent "->" n || isIdent "Primitives.->" n then Just (a, b) else Nothing
getArrow _ = Nothing

getArrows :: EType -> ([EType], EType)
getArrows at =
  case getArrow at of
    Nothing     -> ([], at)
    Just (t, r) -> first (t:) (getArrows r)

mkEStr :: SLoc -> String -> Expr
mkEStr loc str = ESign (ELit loc (LStr str)) $ EListish $ LList [EVar $ mkBuiltin loc "Char"]

-- Make a call to generate an exception with location info
mkExn :: SLoc -> String -> String -> Expr
mkExn loc msg exn =
  let str = mkEStr loc $ msg ++ ", at " ++ show loc
      fn  = ELit loc $ LExn $ "Example." ++ exn
  in  EApp fn str

getAppM :: HasCallStack => EType -> Maybe (Ident, [EType])
getAppM = loop []
  where loop as (EVar i)   = Just (i, as)
        loop as (EApp f a) = loop (a:as) f
        loop as (EParen e) = loop as e
        loop _ _           = Nothing

getApp :: HasCallStack => EType -> (Ident, [EType])
getApp t = fromMaybe (impossibleShow t) $ getAppM t

type TyVar = Ident

freeTyVars :: [EType] -> [TyVar]
-- Get the free TyVars from a type; no duplicates in result
freeTyVars = foldr (go []) []
  where
    go :: [TyVar] -- Ignore occurrences of bound type variables
       -> EType   -- Type to look at
       -> [TyVar] -- Accumulates result
       -> [TyVar]
    go bound (EVar tv) acc
      | tv `elem` bound = acc
      | tv `elem` acc = acc
      | isConIdent tv = acc
      | otherwise = tv : acc
    go bound (EForall _ tvs ty) acc = go (map idKindIdent tvs ++ bound) ty acc
    go bound (EApp fun arg) acc = go bound fun (go bound arg acc)
    go _bound (EUVar _) acc = acc
    go _bound (ECon _) acc = acc
    go _bound (ELit _ _) acc = acc
    go bound (EOper e ies) acc = go bound e (goList bound (map snd ies) acc)
    go bound (ESign e _) acc = go bound e acc
    go bound (EListish (LList [e])) acc = go bound e acc
    go bound (ETuple es) acc = goList bound es acc
    go bound (EParen e) acc = go bound e acc
    go bound (EQVar e _) acc = go bound e acc
    go _ x _ = error ("freeTyVars: " ++ show x) --  impossibleShow x
    goList bound es acc = foldr (go bound) acc es

getImplies :: EType -> Maybe (EType, EType)
getImplies (EApp (EApp (EVar n) a) b) =
  if isIdent "=>" n || isIdent "Primitives.=>" n then Just (a, b) else Nothing
getImplies _ = Nothing
