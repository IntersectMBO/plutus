{-# LANGUAGE CPP #-}

module PlutusTx.Plugin.Deriving.Hs
  ( app
  , bindStmt
  , doExpr
  , explicitList
  , explicitTuple
  , fieldOcc
  , caseMatch
  , funBind
  , funMatch
  , funTy
  , grhs
  , grhss
  , importDecls
  , intLit
  , lam
  , lastStmt
  , letE
  , lit
  , match
  , mg
  , opApp
  , par
  , qual
  , qualTyVar
  , qualVar
  , recField
  , recFields
  , recordCon
  , string
  , tupArg
  , tyVar
  , unqual
  , unrestrictedArrow
  , userTyVar
  , valLocalBinds
  , var
  , varPat
  )
where

#if __GLASGOW_HASKELL__ < 912
import qualified GHC.Data.Bag as Ghc
#endif
import GHC.Hs qualified as Ghc
import GHC.Plugins qualified as Ghc
import GHC.Types.Fixity qualified as Ghc
import GHC.Types.SourceText qualified as Ghc

app
  :: Ghc.SrcSpan
  -> Ghc.LHsExpr Ghc.GhcPs
  -> Ghc.LHsExpr Ghc.GhcPs
  -> Ghc.LHsExpr Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 910
app s f x = Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.HsApp Ghc.noExtField f x)
#else
app s f x = Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.HsApp Ghc.noAnn f x)
#endif

bindStmt
  :: Ghc.SrcSpan
  -> Ghc.LPat Ghc.GhcPs
  -> Ghc.LHsExpr Ghc.GhcPs
  -> Ghc.LStmt Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
bindStmt s p e =
  Ghc.L (Ghc.noAnnSrcSpan s) $ Ghc.BindStmt Ghc.noAnn p e

doExpr :: Ghc.SrcSpan -> [Ghc.ExprLStmt Ghc.GhcPs] -> Ghc.LHsExpr Ghc.GhcPs
doExpr s stmts =
  Ghc.L (Ghc.noAnnSrcSpan s) $
    Ghc.HsDo Ghc.noAnn (Ghc.DoExpr Nothing) (Ghc.L (Ghc.noAnnSrcSpan s) stmts)

explicitList :: Ghc.SrcSpan -> [Ghc.LHsExpr Ghc.GhcPs] -> Ghc.LHsExpr Ghc.GhcPs
explicitList s xs = Ghc.L (Ghc.noAnnSrcSpan s) $ Ghc.ExplicitList Ghc.noAnn xs

explicitTuple :: Ghc.SrcSpan -> [Ghc.HsTupArg Ghc.GhcPs] -> Ghc.LHsExpr Ghc.GhcPs
explicitTuple s xs = Ghc.L (Ghc.noAnnSrcSpan s) $ Ghc.ExplicitTuple Ghc.noAnn xs Ghc.Boxed

fieldOcc :: Ghc.SrcSpan -> Ghc.RdrName -> Ghc.LFieldOcc Ghc.GhcPs
fieldOcc s r =
  Ghc.L (Ghc.noAnnSrcSpan s) $
    Ghc.FieldOcc
      { Ghc.foExt = Ghc.noExtField
      , Ghc.foLabel = Ghc.L (Ghc.noAnnSrcSpan s) r
      }

funBind
  :: Ghc.SrcSpan
  -> Ghc.OccName
  -> Ghc.MatchGroup Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
  -> Ghc.LHsBind Ghc.GhcPs
funBind s f g =
  Ghc.L (Ghc.noAnnSrcSpan s) $ Ghc.FunBind Ghc.noExtField (unqual s f) g

grhs
  :: Ghc.SrcSpan
  -> Ghc.LHsExpr Ghc.GhcPs
  -> Ghc.LGRHS Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
grhs s e = Ghc.L (Ghc.noAnnSrcSpan s) $ Ghc.GRHS Ghc.noAnn [] e

grhss
  :: Ghc.SrcSpan
  -> [Ghc.LGRHS Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)]
  -> Ghc.GRHSs Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
grhss _ xs =
  Ghc.GRHSs Ghc.emptyComments xs $ Ghc.EmptyLocalBinds Ghc.noExtField

importDecl
  :: Ghc.SrcSpan
  -> Ghc.ModuleName
  -> Ghc.ModuleName
  -> Ghc.LImportDecl Ghc.GhcPs
importDecl s m n =
  Ghc.L (Ghc.noAnnSrcSpan s) $
    Ghc.ImportDecl
      { Ghc.ideclExt =
          Ghc.XImportDeclPass
            { Ghc.ideclAnn = Ghc.noAnn
            , Ghc.ideclSourceText = Ghc.NoSourceText
            , Ghc.ideclImplicit = False
            }
      , Ghc.ideclName = Ghc.L (Ghc.noAnnSrcSpan s) m
      , Ghc.ideclPkgQual = Ghc.NoRawPkgQual
      , Ghc.ideclSource = Ghc.NotBoot
      , Ghc.ideclSafe = False
      , Ghc.ideclQualified = Ghc.QualifiedPre
      , Ghc.ideclAs = Just $ Ghc.L (Ghc.noAnnSrcSpan s) n
      , Ghc.ideclImportList = Nothing
      }

importDecls
  :: Ghc.SrcSpan
  -> [(Ghc.ModuleName, Ghc.ModuleName)]
  -> [Ghc.LImportDecl Ghc.GhcPs]
importDecls = fmap . uncurry . importDecl

lam
  :: Ghc.SrcSpan
  -> Ghc.MatchGroup Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
  -> Ghc.LHsExpr Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 910
lam s mg_ = Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.HsLam Ghc.noAnn Ghc.LamSingle mg_)
#else
lam s mg_ = Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.HsLam Ghc.noExtField mg_)
#endif

lastStmt
  :: Ghc.SrcSpan
  -> Ghc.LHsExpr Ghc.GhcPs
  -> Ghc.LStmt Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
lastStmt s e = Ghc.L (Ghc.noAnnSrcSpan s) $ Ghc.LastStmt Ghc.noExtField e Nothing noSyntaxExpr

lit :: Ghc.SrcSpan -> Ghc.HsLit Ghc.GhcPs -> Ghc.LHsExpr Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 910
lit s l = Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.HsLit Ghc.noExtField l)
#else
lit s l = Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.HsLit Ghc.noAnn l)
#endif

noSyntaxExpr :: Ghc.SyntaxExpr Ghc.GhcPs
noSyntaxExpr = Ghc.noSyntaxExpr

{-| Build a lambda match. The match context is always a (single) lambda,
so it is baked in rather than passed by the caller; this also avoids a
CPP-divergent context type in the signature. -}
match
  :: Ghc.SrcSpan
  -> [Ghc.LPat Ghc.GhcPs]
  -> Ghc.GRHSs Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
  -> Ghc.LMatch Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
#if __GLASGOW_HASKELL__ >= 910
match s ps g =
  Ghc.L (Ghc.noAnnSrcSpan s)
    (Ghc.Match Ghc.noExtField (Ghc.LamAlt Ghc.LamSingle) (Ghc.L (Ghc.noAnnSrcSpan s) ps) g)
#else
match s ps g =
  Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.Match Ghc.noAnn Ghc.LambdaExpr ps g)
#endif

{-| A prefix-function ('FunRhs') match with located patterns. @FunRhs@ gained
an annotation field and @m_pats@ became located in GHC 9.10. -}
funMatch
  :: Ghc.SrcSpan
  -> Ghc.LIdP Ghc.GhcPs
  -> [Ghc.LPat Ghc.GhcPs]
  -> Ghc.GRHSs Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
  -> Ghc.LMatch Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
#if __GLASGOW_HASKELL__ >= 910
funMatch s v ps g =
  Ghc.L (Ghc.noAnnSrcSpan s)
    (Ghc.Match Ghc.noExtField (Ghc.FunRhs v Ghc.Prefix Ghc.NoSrcStrict Ghc.noAnn) (Ghc.L (Ghc.noAnnSrcSpan s) ps) g)
#else
funMatch s v ps g =
  Ghc.L (Ghc.noAnnSrcSpan s)
    (Ghc.Match Ghc.noAnn (Ghc.FunRhs v Ghc.Prefix Ghc.NoSrcStrict) ps g)
#endif

-- | A @case@ alternative ('CaseAlt') match with located patterns.
caseMatch
  :: Ghc.SrcSpan
  -> [Ghc.LPat Ghc.GhcPs]
  -> Ghc.GRHSs Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
  -> Ghc.LMatch Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
#if __GLASGOW_HASKELL__ >= 910
caseMatch s ps g =
  Ghc.L (Ghc.noAnnSrcSpan s)
    (Ghc.Match Ghc.noExtField Ghc.CaseAlt (Ghc.L (Ghc.noAnnSrcSpan s) ps) g)
#else
caseMatch s ps g =
  Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.Match Ghc.noAnn Ghc.CaseAlt ps g)
#endif

{-| A @let ... in ...@ expression. The @let@/@in@ tokens moved into the
extension field in GHC 9.10. -}
letE
  :: Ghc.SrcSpan
  -> Ghc.HsLocalBinds Ghc.GhcPs
  -> Ghc.LHsExpr Ghc.GhcPs
  -> Ghc.LHsExpr Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 910
letE s binds body =
  Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.HsLet Ghc.noAnn binds body)
#else
letE s binds body =
  Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.HsLet Ghc.noAnn Ghc.noHsTok binds Ghc.noHsTok body)
#endif

{-| A function type @a -> b@ (unrestricted arrow). The @HsFunTy@ extension
field became 'Ghc.NoExtField' in GHC 9.10. -}
funTy
  :: Ghc.SrcSpan
  -> Ghc.LHsType Ghc.GhcPs
  -> Ghc.LHsType Ghc.GhcPs
  -> Ghc.LHsType Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 910
funTy s a b =
  Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.HsFunTy Ghc.noExtField unrestrictedArrow a b)
#else
funTy s a b =
  Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.HsFunTy Ghc.noAnn unrestrictedArrow a b)
#endif

{-| An integer overloaded literal. The @HsOverLit@ extension field became
'Ghc.NoExtField' in GHC 9.10. -}
intLit :: Ghc.SrcSpan -> Integer -> Ghc.LHsExpr Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 910
intLit s n =
  Ghc.L (Ghc.noAnnSrcSpan s)
    (Ghc.HsOverLit Ghc.noExtField
      (Ghc.OverLit Ghc.noExtField (Ghc.HsIntegral (Ghc.IL Ghc.NoSourceText False n))))
#else
intLit s n =
  Ghc.L (Ghc.noAnnSrcSpan s)
    (Ghc.HsOverLit Ghc.noAnn
      (Ghc.OverLit Ghc.noExtField (Ghc.HsIntegral (Ghc.IL Ghc.NoSourceText False n))))
#endif

{-| The unrestricted function arrow @->@. Its token representation moved
into an annotation in GHC 9.10. -}
unrestrictedArrow :: Ghc.HsArrow Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 910
unrestrictedArrow = Ghc.HsUnrestrictedArrow Ghc.noAnn
#else
unrestrictedArrow = Ghc.HsUnrestrictedArrow Ghc.noHsUniTok
#endif

{-| Value local-bindings from a list of binds. @LHsBinds@ became a plain
list (was a @Bag@) in GHC 9.12. -}
valLocalBinds :: [Ghc.LHsBind Ghc.GhcPs] -> Ghc.HsLocalBinds Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 912
valLocalBinds binds =
  Ghc.HsValBinds Ghc.noAnn (Ghc.ValBinds Ghc.NoAnnSortKey binds [])
#else
valLocalBinds binds =
  Ghc.HsValBinds Ghc.noAnn (Ghc.ValBinds Ghc.NoAnnSortKey (Ghc.listToBag binds) [])
#endif

{-| A user type-variable binder with no kind annotation. The binder layout
changed to @HsTvb@/@HsBndrVar@ in GHC 9.10, and the binder visibility flag
(@HsBndrVis@) replaced the unit flag for these binders. -}
userTyVar
  :: Ghc.SrcSpan
  -> Ghc.IdP Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 910
  -> Ghc.LHsTyVarBndr (Ghc.HsBndrVis Ghc.GhcPs) Ghc.GhcPs
#else
  -> Ghc.LHsTyVarBndr () Ghc.GhcPs
#endif
#if __GLASGOW_HASKELL__ >= 910
userTyVar s v =
  Ghc.L (Ghc.noAnnSrcSpan s)
    (Ghc.HsTvb Ghc.noAnn (Ghc.HsBndrRequired Ghc.noExtField) (Ghc.HsBndrVar Ghc.noExtField (Ghc.L (Ghc.noAnnSrcSpan s) v)) (Ghc.HsBndrNoKind Ghc.noExtField))
#else
userTyVar s v =
  Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.UserTyVar Ghc.noAnn () (Ghc.L (Ghc.noAnnSrcSpan s) v))
#endif

mg
  :: Ghc.Located [Ghc.LMatch Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)]
  -> Ghc.MatchGroup Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
#if __GLASGOW_HASKELL__ >= 910
mg ms = Ghc.MG (Ghc.Generated Ghc.OtherExpansion Ghc.SkipPmc) (Ghc.noLocA (Ghc.unLoc ms))
#else
mg ms = Ghc.MG Ghc.Generated (Ghc.noLocA (Ghc.unLoc ms))
#endif

opApp
  :: Ghc.SrcSpan
  -> Ghc.LHsExpr Ghc.GhcPs
  -> Ghc.LHsExpr Ghc.GhcPs
  -> Ghc.LHsExpr Ghc.GhcPs
  -> Ghc.LHsExpr Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 910
opApp s l o r = Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.OpApp Ghc.noExtField l o r)
#else
opApp s l o r = Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.OpApp Ghc.noAnn l o r)
#endif

par :: Ghc.SrcSpan -> Ghc.LHsExpr Ghc.GhcPs -> Ghc.LHsExpr Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 910
par s e = Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.HsPar Ghc.noAnn e)
#else
par s e = Ghc.L (Ghc.noAnnSrcSpan s) (Ghc.HsPar Ghc.noAnn Ghc.noHsTok e Ghc.noHsTok)
#endif

qual :: Ghc.SrcSpan -> Ghc.ModuleName -> Ghc.OccName -> Ghc.LIdP Ghc.GhcPs
qual s m n = Ghc.L (Ghc.noAnnSrcSpan s) $ Ghc.mkRdrQual m n

qualTyVar :: Ghc.SrcSpan -> Ghc.ModuleName -> Ghc.OccName -> Ghc.LHsType Ghc.GhcPs
qualTyVar s m = tyVar s . qual s m

qualVar :: Ghc.SrcSpan -> Ghc.ModuleName -> Ghc.OccName -> Ghc.LHsExpr Ghc.GhcPs
qualVar s m = var s . qual s m

recFields
  :: [Ghc.LHsRecField Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)]
  -> Ghc.HsRecFields Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
#if __GLASGOW_HASKELL__ >= 910
recFields fs = Ghc.HsRecFields Ghc.noExtField fs Nothing
#else
recFields fs = Ghc.HsRecFields fs Nothing
#endif

recField
  :: Ghc.SrcSpan
  -> Ghc.LFieldOcc Ghc.GhcPs
  -> Ghc.LHsExpr Ghc.GhcPs
  -> Ghc.LHsRecField Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
recField s f e = Ghc.L (Ghc.noAnnSrcSpan s) $ Ghc.HsFieldBind Ghc.noAnn f e False

recordCon
  :: Ghc.SrcSpan
  -> Ghc.LIdP Ghc.GhcPs
  -> Ghc.HsRecordBinds Ghc.GhcPs
  -> Ghc.LHsExpr Ghc.GhcPs
recordCon s c fs = Ghc.L (Ghc.noAnnSrcSpan s) $ Ghc.RecordCon Ghc.noAnn c fs

string :: String -> Ghc.HsLit Ghc.GhcPs
string = Ghc.HsString Ghc.NoSourceText . Ghc.mkFastString

tupArg :: Ghc.LHsExpr Ghc.GhcPs -> Ghc.HsTupArg Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 910
tupArg = Ghc.Present Ghc.noExtField
#else
tupArg = Ghc.Present Ghc.noAnn
#endif

tyVar :: Ghc.SrcSpan -> Ghc.LIdP Ghc.GhcPs -> Ghc.LHsType Ghc.GhcPs
tyVar s x = Ghc.L (Ghc.noAnnSrcSpan s) $ Ghc.HsTyVar Ghc.noAnn Ghc.NotPromoted x

unqual :: Ghc.SrcSpan -> Ghc.OccName -> Ghc.LIdP Ghc.GhcPs
unqual s n = Ghc.L (Ghc.noAnnSrcSpan s) $ Ghc.mkRdrUnqual n

var :: Ghc.SrcSpan -> Ghc.LIdP Ghc.GhcPs -> Ghc.LHsExpr Ghc.GhcPs
var s x = Ghc.L (Ghc.noAnnSrcSpan s) $ Ghc.HsVar Ghc.noExtField x

varPat :: Ghc.SrcSpan -> Ghc.LIdP Ghc.GhcPs -> Ghc.LPat Ghc.GhcPs
varPat s x = Ghc.L (Ghc.noAnnSrcSpan s) $ Ghc.VarPat Ghc.noExtField x
