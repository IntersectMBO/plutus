module PlutusTx.Plugin.Deriving.Generator.Optics
  ( generate
  )
where

import Data.List qualified as List
import GHC.Hs qualified as Ghc
import GHC.Plugins qualified as Ghc
import PlutusTx.Plugin.Deriving.Constant.Module qualified as Module
import PlutusTx.Plugin.Deriving.Generator.Common qualified as Common
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
  let lImportDecls = Hs.importDecls srcSpan [(Module.controlLens, lens)]
  decls <- mapM (makePrismDecls srcSpan type_ lens) (Type.constructors type_)
  pure (False, lImportDecls, concat decls)

-- | Generates the signature and binding for one prism.
makePrismDecls
  :: Ghc.SrcSpan
  -> Type.Type
  -> Ghc.ModuleName
  -> Constructor.Constructor
  -> Ghc.Hsc [Ghc.LHsDecl Ghc.GhcPs]
makePrismDecls srcSpan type_ lens constructor = do
  let fields = Constructor.fields constructor
      arity = length fields
      conOcc = Ghc.rdrNameOcc (Constructor.name constructor)
      prismOcc = Ghc.mkVarOcc ("_" <> Ghc.occNameString conOcc)
      prismId = Ghc.L (Ghc.noAnnSrcSpan srcSpan) (Ghc.Unqual prismOcc)
      lConId = Ghc.L (Ghc.noAnnSrcSpan srcSpan) (Ghc.mkRdrUnqual conOcc)

  vars <- mapM (\_ -> Common.makeRandomVariable srcSpan "x_") fields
  scrutVar <- Common.makeRandomVariable srcSpan "x_"

  let
    -- Focus type: () / T / (T0, T1, ...)
    fieldTys = fmap (\f -> Ghc.L (Ghc.noAnnSrcSpan srcSpan) (Field.type_ f)) fields
    focusTy = case fieldTys of
      [] -> unitTy srcSpan
      [ft] -> ft
      _ ->
        Ghc.L (Ghc.noAnnSrcSpan srcSpan) $ Ghc.HsTupleTy Ghc.noAnn Ghc.HsBoxedOrConstraintTuple fieldTys

    -- Outer type: TypeName a b ...
    outerTy = mkOuterTy srcSpan type_

    -- Prism' OuterTy FocusTy
    prismTy =
      Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
        Ghc.HsAppTy
          Ghc.noExtField
          ( Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
              Ghc.HsAppTy
                Ghc.noExtField
                ( Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
                    Ghc.HsTyVar
                      Ghc.noAnn
                      Ghc.NotPromoted
                      (Ghc.L (Ghc.noAnnSrcSpan srcSpan) $ Ghc.Qual lens (Ghc.mkTcOcc "Prism'"))
                )
                outerTy
          )
          focusTy

    -- _ConName :: Prism' OuterTy FocusTy
    sigDecl =
      Ghc.noLocA $
        Ghc.SigD Ghc.noExtField $
          Ghc.TypeSig Ghc.noAnn [prismId] $
            Ghc.HsWC Ghc.noExtField $
              Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
                Ghc.HsSig Ghc.noExtField Ghc.mkHsOuterImplicit prismTy

    -- _ConName = lens.prism' builder matcher
    prismExpr =
      Hs.app
        srcSpan
        ( Hs.app
            srcSpan
            (Hs.qualVar srcSpan lens (Ghc.mkVarOcc "prism'"))
            (Hs.par srcSpan $ mkBuilder srcSpan lConId vars arity)
        )
        (Hs.par srcSpan $ mkMatcher srcSpan lConId vars scrutVar arity)

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
mkBuilder srcSpan lConId vars arity = case arity of
  0 ->
    Hs.app
      srcSpan
      (Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkVarOcc "const")))
      (Hs.var srcSpan lConId)
  1 ->
    Hs.var srcSpan lConId
  _ ->
    let tuplePat =
          Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
            Ghc.TuplePat Ghc.noAnn (fmap (Hs.varPat srcSpan) vars) Ghc.Boxed
        body = List.foldl' (Hs.app srcSpan) (Hs.var srcSpan lConId) (fmap (Hs.var srcSpan) vars)
     in Hs.lam srcSpan . Hs.mg $
          Ghc.L
            srcSpan
            [Hs.match srcSpan [tuplePat] (Common.makeGRHSs srcSpan body)]

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
  let just = Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkDataOcc "Just"))
      successResult = case vars of
        [] ->
          Hs.app srcSpan just (unitExpr srcSpan)
        [v] ->
          Hs.app srcSpan just (Hs.par srcSpan $ Hs.var srcSpan v)
        _ ->
          Hs.app srcSpan just $
            Hs.par srcSpan $
              Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
                Ghc.ExplicitTuple Ghc.noAnn (fmap (Hs.tupArg . Hs.var srcSpan) vars) Ghc.Boxed

      conPat =
        Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
          Ghc.ConPat Ghc.noAnn lConId (Ghc.PrefixCon [] (fmap (Hs.varPat srcSpan) vars))

      wildPat = Ghc.L (Ghc.noAnnSrcSpan srcSpan) $ Ghc.WildPat Ghc.noExtField

      nothingExpr = Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkDataOcc "Nothing"))

      conMatch =
        Hs.caseMatch srcSpan [conPat] (Common.makeGRHSs srcSpan successResult)

      wildMatch =
        Hs.caseMatch srcSpan [wildPat] (Common.makeGRHSs srcSpan nothingExpr)

      caseExpr =
        Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
          Ghc.HsCase
            Ghc.noAnn
            (Hs.var srcSpan scrutVar)
            (Hs.mg (Ghc.L srcSpan [conMatch, wildMatch]))
   in Hs.lam srcSpan . Hs.mg $
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
    tv n = Hs.tyVar srcSpan (Ghc.L (Ghc.noAnnSrcSpan srcSpan) n)

    initial :: Ghc.LHsType Ghc.GhcPs
    initial = tv (Type.name type_)

    applied :: Ghc.LHsType Ghc.GhcPs
    applied =
      List.foldl'
        ( \acc v ->
            Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
              Ghc.HsAppTy Ghc.noExtField acc (tv v)
        )
        initial
        (Type.variables type_)
   in
    case Type.variables type_ of
      [] -> applied
      _ -> Ghc.L (Ghc.noAnnSrcSpan srcSpan) $ Ghc.HsParTy Ghc.noAnn applied

-- | The unit type @()@ at the type level.
unitTy :: Ghc.SrcSpan -> Ghc.LHsType Ghc.GhcPs
unitTy srcSpan =
  Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
    Ghc.HsTupleTy Ghc.noAnn Ghc.HsBoxedOrConstraintTuple []

-- | The unit expression @()@.
unitExpr :: Ghc.SrcSpan -> Ghc.LHsExpr Ghc.GhcPs
unitExpr srcSpan =
  Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
    Ghc.ExplicitTuple Ghc.noAnn [] Ghc.Boxed
