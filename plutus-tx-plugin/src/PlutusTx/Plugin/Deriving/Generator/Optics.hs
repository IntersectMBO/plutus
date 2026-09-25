module PlutusTx.Plugin.Deriving.Generator.Optics
  ( generate
  )
where

import Data.List qualified as List
import Data.Traversable (for)
import GHC.Hs qualified as Ghc
import GHC.Plugins qualified as Ghc
import PlutusTx.Plugin.Deriving.Constant.Module qualified as Module
import PlutusTx.Plugin.Deriving.Generator.Common qualified as Common
import PlutusTx.Plugin.Deriving.Hs (loc)
import PlutusTx.Plugin.Deriving.Hs qualified as Hs
import PlutusTx.Plugin.Deriving.Type.Constructor qualified as Constructor
import PlutusTx.Plugin.Deriving.Type.Field qualified as Field
import PlutusTx.Plugin.Deriving.Type.Type qualified as Type

{-| For each constructor generates a 'Prism'' binding. For example:

> data Shape = Point | Circle Integer | Rectangle Integer Integer
>   deriving Optics via Plinth

Produces:

> _Point     :: Prism' Shape ()
> _Circle    :: Prism' Shape Integer
> _Rectangle :: Prism' Shape (Integer, Integer) -}
generate :: Ghc.HsDeriving Ghc.GhcPs -> Common.Generator
generate _ _moduleName lIdP lHsQTyVars lConDecls srcSpan = do
  type_ <- Type.make lIdP lHsQTyVars lConDecls srcSpan
  lens <- Common.makeRandomModule Module.controlLens
  let lImportDecls :: [Ghc.LImportDecl Ghc.GhcPs]
      lImportDecls = Hs.importDecls srcSpan [(Module.controlLens, lens)]
  decls <- for (Type.constructors type_) (makePrismDecls srcSpan type_ lens)
  pure (False, lImportDecls, concat decls)

-- | Generates the signature and binding for one prism.
makePrismDecls
  :: Ghc.SrcSpan
  -> Type.Type
  -> Ghc.ModuleName
  -> Constructor.Constructor
  -> Ghc.Hsc [Ghc.LHsDecl Ghc.GhcPs]
makePrismDecls srcSpan type_ lens constructor = do
  let
    fields :: [Field.Field]
    fields = Constructor.fields constructor

    arity :: Int
    arity = length fields

    conOcc :: Ghc.OccName
    conOcc = Ghc.rdrNameOcc (Constructor.name constructor)

    prismOcc :: Ghc.OccName
    prismOcc = Ghc.mkVarOcc ("_" <> Ghc.occNameString conOcc)

    prismId :: Ghc.LIdP Ghc.GhcPs
    prismId = loc srcSpan (Ghc.Unqual prismOcc)

    lConId :: Ghc.LIdP Ghc.GhcPs
    lConId = loc srcSpan (Ghc.mkRdrUnqual conOcc)

  vars <- for fields \_ -> Common.makeRandomVariable srcSpan "x_"
  scrutVar <- Common.makeRandomVariable srcSpan "x_"

  let
    -- Focus type: () / T / (T0, T1, ...)
    fieldTys :: [Ghc.LHsType Ghc.GhcPs]
    fieldTys = fmap (\f -> loc srcSpan (Field.type_ f)) fields

    focusTy :: Ghc.LHsType Ghc.GhcPs
    focusTy = case fieldTys of
      [] -> unitTy srcSpan
      [ft] -> ft
      _ ->
        loc srcSpan $ Ghc.HsTupleTy Ghc.noAnn Ghc.HsBoxedOrConstraintTuple fieldTys

    -- Outer type: TypeName a b ...
    outerTy :: Ghc.LHsType Ghc.GhcPs
    outerTy = mkOuterTy srcSpan type_

    -- Prism' OuterTy FocusTy
    prismTy :: Ghc.LHsType Ghc.GhcPs
    prismTy =
      loc srcSpan do
        Ghc.HsAppTy
          Ghc.noExtField
          ( loc srcSpan do
              Ghc.HsAppTy
                Ghc.noExtField
                ( loc srcSpan do
                    Ghc.HsTyVar
                      Ghc.noAnn
                      Ghc.NotPromoted
                      (loc srcSpan $ Ghc.Qual lens (Ghc.mkTcOcc "Prism'"))
                )
                outerTy
          )
          focusTy

    -- _ConName :: Prism' OuterTy FocusTy
    sigDecl :: Ghc.LHsDecl Ghc.GhcPs
    sigDecl =
      Ghc.noLocA $
        Ghc.SigD Ghc.noExtField $
          Ghc.TypeSig Ghc.noAnn [prismId] $
            Ghc.HsWC Ghc.noExtField $
              loc srcSpan do
                Ghc.HsSig Ghc.noExtField Ghc.mkHsOuterImplicit prismTy

    -- _ConName = lens.prism' builder matcher
    prismExpr :: Ghc.LHsExpr Ghc.GhcPs
    prismExpr =
      Hs.app
        srcSpan
        ( Hs.app
            srcSpan
            (Hs.qualVar srcSpan lens (Ghc.mkVarOcc "prism'"))
            (Hs.par srcSpan $ mkBuilder srcSpan lConId vars arity)
        )
        (Hs.par srcSpan $ mkMatcher srcSpan lConId vars scrutVar arity)

    valDecl :: Ghc.LHsDecl Ghc.GhcPs
    valDecl =
      Ghc.noLocA $
        Ghc.ValD Ghc.noExtField $
          Ghc.FunBind
            Ghc.noExtField
            prismId
            (Hs.mg (Ghc.L srcSpan [Hs.funMatch srcSpan prismId [] (Common.makeGRHSs srcSpan prismExpr)]))

  pure [sigDecl, valDecl]

{-| Builder function: converts the focus type back to the sum type.

* Nullary: @const ConName@
* Unary:   @ConName@
* Multi:   @\(x0, x1, ...) -> ConName x0 x1 ...@ -}
mkBuilder
  :: Ghc.SrcSpan
  -> Ghc.LIdP Ghc.GhcPs
  -> [Ghc.LIdP Ghc.GhcPs]
  -> Int
  -> Ghc.LHsExpr Ghc.GhcPs
mkBuilder srcSpan lConId vars = \case
  0 ->
    Hs.app
      srcSpan
      (Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkVarOcc "const")))
      (Hs.var srcSpan lConId)
  1 ->
    Hs.var srcSpan lConId
  _ ->
    Hs.lam srcSpan $
      Hs.mg $
        Ghc.L
          srcSpan
          [Hs.match srcSpan [tuplePat] (Common.makeGRHSs srcSpan body)]
    where
      tuplePat :: Ghc.LPat Ghc.GhcPs
      tuplePat =
        loc srcSpan do
          Ghc.TuplePat Ghc.noAnn (fmap (Hs.varPat srcSpan) vars) Ghc.Boxed

      body :: Ghc.LHsExpr Ghc.GhcPs
      body =
        List.foldl'
          (Hs.app srcSpan)
          (Hs.var srcSpan lConId)
          (Hs.var srcSpan <$> vars)

{-| Matcher function: converts the sum type to @Maybe@ focus.

@\x -> case x of { ConName x0 x1 ... -> Just (x0, x1, ...); _ -> Nothing }@ -}
mkMatcher
  :: Ghc.SrcSpan
  -> Ghc.LIdP Ghc.GhcPs
  -> [Ghc.LIdP Ghc.GhcPs]
  -> Ghc.LIdP Ghc.GhcPs
  -> Int
  -> Ghc.LHsExpr Ghc.GhcPs
mkMatcher srcSpan lConId vars scrutVar _arity =
  let
    just :: Ghc.LHsExpr Ghc.GhcPs
    just = Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkDataOcc "Just"))

    successResult :: Ghc.LHsExpr Ghc.GhcPs
    successResult
      | [] <- vars =
          Hs.app srcSpan just $ unitExpr srcSpan
      | [v] <- vars =
          Hs.app srcSpan just $ Hs.par srcSpan $ Hs.var srcSpan v
      | otherwise =
          Hs.app srcSpan just $
            Hs.par srcSpan $
              loc srcSpan do
                Ghc.ExplicitTuple Ghc.noAnn (fmap (Hs.tupArg . Hs.var srcSpan) vars) Ghc.Boxed

    conPat :: Ghc.LPat Ghc.GhcPs
    conPat =
      loc srcSpan do
        Ghc.ConPat Ghc.noAnn lConId $
          Ghc.PrefixCon [] (Hs.varPat srcSpan <$> vars)

    wildPat :: Ghc.LPat Ghc.GhcPs
    wildPat = loc srcSpan $ Ghc.WildPat Ghc.noExtField

    nothingExpr :: Ghc.LHsExpr Ghc.GhcPs
    nothingExpr = Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkDataOcc "Nothing"))

    conMatch :: Ghc.LMatch Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
    conMatch =
      Hs.caseMatch srcSpan [conPat] (Common.makeGRHSs srcSpan successResult)

    wildMatch :: Ghc.LMatch Ghc.GhcPs (Ghc.LHsExpr Ghc.GhcPs)
    wildMatch =
      Hs.caseMatch srcSpan [wildPat] (Common.makeGRHSs srcSpan nothingExpr)

    caseExpr :: Ghc.LHsExpr Ghc.GhcPs
    caseExpr =
      loc srcSpan do
        Ghc.HsCase
          Ghc.noAnn
          (Hs.var srcSpan scrutVar)
          (Hs.mg (Ghc.L srcSpan [conMatch, wildMatch]))
   in
    Hs.lam srcSpan . Hs.mg $
      Ghc.L
        srcSpan
        [ Hs.match
            srcSpan
            [Hs.varPat srcSpan scrutVar]
            (Common.makeGRHSs srcSpan caseExpr)
        ]

{-| Build @TypeName a b ...@ as an 'LHsType', parenthesised when there are
type variables (so it can be applied to the focus type without ambiguity). -}
mkOuterTy :: Ghc.SrcSpan -> Type.Type -> Ghc.LHsType Ghc.GhcPs
mkOuterTy srcSpan type_ =
  let
    -- Each location wrapper is a fresh expression so its annotation type is
    -- inferred per-position (a shared @loc@ monomorphises to the wrong one).
    tv :: Ghc.IdP Ghc.GhcPs -> Ghc.LHsType Ghc.GhcPs
    tv = Hs.tyVar srcSpan . loc srcSpan

    initial :: Ghc.LHsType Ghc.GhcPs
    initial = tv (Type.name type_)

    applied :: Ghc.LHsType Ghc.GhcPs
    applied =
      List.foldl'
        ( \acc v ->
            loc srcSpan do
              Ghc.HsAppTy Ghc.noExtField acc (tv v)
        )
        initial
        (Type.variables type_)
   in
    case Type.variables type_ of
      [] -> applied
      _ -> loc srcSpan $ Ghc.HsParTy Ghc.noAnn applied

-- | The unit type @()@ at the type level.
unitTy :: Ghc.SrcSpan -> Ghc.LHsType Ghc.GhcPs
unitTy srcSpan =
  loc srcSpan do
    Ghc.HsTupleTy Ghc.noAnn Ghc.HsBoxedOrConstraintTuple []

-- | The unit expression @()@.
unitExpr :: Ghc.SrcSpan -> Ghc.LHsExpr Ghc.GhcPs
unitExpr srcSpan =
  loc srcSpan do
    Ghc.ExplicitTuple Ghc.noAnn [] Ghc.Boxed
