{-# LANGUAGE CPP #-}

module PlutusTx.Plugin.Deriving.Generator.AsData
  ( generate
  )
where

import GHC.Hs qualified as Ghc
import GHC.Plugins qualified as Ghc
import GHC.Types.Fixity qualified as Ghc
import GHC.Types.SourceText qualified as Ghc
import PlutusTx.Plugin.Deriving.Constant.Module qualified as Module
import PlutusTx.Plugin.Deriving.Generator.Common qualified as Common
import PlutusTx.Plugin.Deriving.Hs qualified as Hs
import PlutusTx.Plugin.Deriving.Hsc qualified as Hsc
import PlutusTx.Plugin.Deriving.Type.Constructor qualified as Constructor
import PlutusTx.Plugin.Deriving.Type.Field qualified as Field
import PlutusTx.Plugin.Deriving.Type.Type qualified as Type

{-| Replaces the original data declaration with a newtype backed by
'BuiltinData', generates bidirectional pattern synonyms for each
constructor, and derives 'ToData'/'FromData' via GND.

Given:

> data Example a = Ex1 Integer | Ex2 a a
>   deriving AsData via Plinth

Generates:

> newtype Example a = Example_BD PlutusTx.Builtins.BuiltinData
>   deriving newtype (PlutusTx.ToData, PlutusTx.FromData)
>
> pattern Ex1 :: Integer -> Example a
> pattern Ex1 x0_ <-
>   Example_BD ((\d_ -> PlutusTx.unsafeFromBuiltinData
>     (PlutusTx.headBuiltinList (PlutusTx.sndPair (PlutusTx.unsafeDataAsConstr d_)))) -> x0_)
>   where Ex1 x0_ = Example_BD (PlutusTx.mkConstr 0 [PlutusTx.toBuiltinData x0_])
>
> pattern Ex2 :: a -> a -> Example a
> pattern Ex2 x0_ x1_ <-
>   Example_BD ((\d_ -> let args_ = PlutusTx.sndPair (PlutusTx.unsafeDataAsConstr d_)
>                        in (PlutusTx.unsafeFromBuiltinData (PlutusTx.headBuiltinList args_),
>                            ...)) -> (x0_, x1_))
>   where Ex2 x0_ x1_ = Example_BD (PlutusTx.mkConstr 1 [...])
>
> {\-# COMPLETE Ex1, Ex2 #-\} -}
generate :: Ghc.HsDeriving Ghc.GhcPs -> Common.Generator
generate remainingDerivs _moduleName lIdP lHsQTyVars lConDecls srcSpan = do
  type_ <- Type.make lIdP lHsQTyVars lConDecls srcSpan
  let constructors = Type.constructors type_
  when (null constructors) $
    Hsc.throwError srcSpan $
      Ghc.text "AsData requires at least one constructor"

  plutusTx <- Common.makeRandomModule Module.plutusTx
  plutusTxBuiltins <- Common.makeRandomModule Module.plutusTxBuiltins

  let lImportDecls =
        Hs.importDecls
          srcSpan
          [ (Module.plutusTx, plutusTx)
          , (Module.plutusTxBuiltins, plutusTxBuiltins)
          ]

      newtypeDecl =
        makeNewtypeDecl srcSpan type_ plutusTx plutusTxBuiltins remainingDerivs

      completeDecl =
        makeCompleteDecl srcSpan constructors

  patSynDecls <-
    mapM
      (\(idx, con) -> makePatSynDecl srcSpan type_ con idx plutusTx plutusTxBuiltins)
      (zip [0 ..] constructors)

  pure (True, lImportDecls, newtypeDecl : concat patSynDecls <> [completeDecl])

when :: Applicative f => Bool -> f () -> f ()
when True action = action
when False _ = pure ()

-- | The internal constructor name for the newtype.
internalConName :: Type.Type -> Ghc.OccName
internalConName type_ =
  Ghc.mkDataOcc $
    Ghc.occNameString (Ghc.rdrNameOcc (Type.name type_)) <> "_BD"

{-| Build an 'Ghc.HsDataDefn'. CPP-shimmed because the @dd_ext@ field's value
(@noAnn@ vs @noExtField@) changed in GHC 9.10. -}
mkDataDefn
  :: Ghc.DataDefnCons (Ghc.LConDecl Ghc.GhcPs)
  -> Ghc.HsDeriving Ghc.GhcPs
  -> Ghc.HsDataDefn Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 910
mkDataDefn cons derivs = Ghc.HsDataDefn
  { Ghc.dd_ext     = Ghc.noAnn
  , Ghc.dd_ctxt    = Nothing
  , Ghc.dd_cType   = Nothing
  , Ghc.dd_kindSig = Nothing
  , Ghc.dd_cons    = cons
  , Ghc.dd_derivs  = derivs
  }
#else
mkDataDefn cons derivs = Ghc.HsDataDefn
  { Ghc.dd_ext     = Ghc.noExtField
  , Ghc.dd_ctxt    = Nothing
  , Ghc.dd_cType   = Nothing
  , Ghc.dd_kindSig = Nothing
  , Ghc.dd_cons    = cons
  , Ghc.dd_derivs  = derivs
  }
#endif

{-| Build an 'Ghc.DataDecl'. CPP-shimmed because @tcdDExt@'s value
(@noExtField@ vs @noAnn@) changed in GHC 9.10. -}
mkDataDecl
  :: Ghc.LIdP Ghc.GhcPs
  -> Ghc.LHsQTyVars Ghc.GhcPs
  -> Ghc.HsDataDefn Ghc.GhcPs
  -> Ghc.TyClDecl Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 910
mkDataDecl lname tyVars defn = Ghc.DataDecl
  { Ghc.tcdDExt     = Ghc.noExtField
  , Ghc.tcdLName    = lname
  , Ghc.tcdTyVars   = tyVars
  , Ghc.tcdFixity   = Ghc.Prefix
  , Ghc.tcdDataDefn = defn
  }
#else
mkDataDecl lname tyVars defn = Ghc.DataDecl
  { Ghc.tcdDExt     = Ghc.noAnn
  , Ghc.tcdLName    = lname
  , Ghc.tcdTyVars   = tyVars
  , Ghc.tcdFixity   = Ghc.Prefix
  , Ghc.tcdDataDefn = defn
  }
#endif

{-| Generate: @newtype Example a = Example_BD BuiltinData@
@  deriving newtype (ToData, FromData)@ -}
makeNewtypeDecl
  :: Ghc.SrcSpan
  -> Type.Type
  -> Ghc.ModuleName
  -> Ghc.ModuleName
  -> Ghc.HsDeriving Ghc.GhcPs
  -> Ghc.LHsDecl Ghc.GhcPs
makeNewtypeDecl srcSpan type_ plutusTx plutusTxBuiltins remainingDerivs =
  let tyName = Ghc.rdrNameOcc $ Type.name type_
      lTypeName = Ghc.noLocA $ Ghc.mkRdrUnqual tyName
      lConName = Ghc.noLocA $ Ghc.mkRdrUnqual (internalConName type_)

      builtinDataTy =
        Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
          Ghc.HsTyVar
            Ghc.noAnn
            Ghc.NotPromoted
            (Ghc.L (Ghc.noAnnSrcSpan srcSpan) $ Ghc.Qual plutusTxBuiltins (Ghc.mkTcOcc "BuiltinData"))

      conDecl =
        Ghc.noLocA $
          Ghc.ConDeclH98
            { Ghc.con_ext = Ghc.noAnn
            , Ghc.con_name = lConName
            , Ghc.con_forall = False
            , Ghc.con_ex_tvs = []
            , Ghc.con_mb_cxt = Nothing
            , Ghc.con_args =
                Ghc.PrefixCon
                  []
                  [Ghc.HsScaled Hs.unrestrictedArrow builtinDataTy]
            , Ghc.con_doc = Nothing
            }

      -- deriving newtype (ToData, FromData) plus any remaining clauses
      gndClause = makeGndClause srcSpan plutusTx
      derivs = gndClause : remainingDerivs

      dataDefn = mkDataDefn (Ghc.NewTypeCon conDecl) derivs

      -- Preserve type variables from the original type
      tyVars = mkTyVars srcSpan (Type.variables type_)

      tyClDecl = mkDataDecl lTypeName tyVars dataDefn
   in Ghc.noLocA (Ghc.TyClD Ghc.noExtField tyClDecl)

-- | Build @deriving newtype (PlutusTx.ToData, PlutusTx.FromData)@.
makeGndClause
  :: Ghc.SrcSpan
  -> Ghc.ModuleName
  -> Ghc.LHsDerivingClause Ghc.GhcPs
makeGndClause srcSpan plutusTx =
  let strategy =
        Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
          Ghc.NewtypeStrategy Ghc.noAnn

      mkCls :: Ghc.OccName -> Ghc.LHsSigType Ghc.GhcPs
      mkCls occ =
        Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
          Ghc.HsSig
            Ghc.noExtField
            Ghc.mkHsOuterImplicit
            ( Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
                Ghc.HsTyVar
                  Ghc.noAnn
                  Ghc.NotPromoted
                  (Ghc.L (Ghc.noAnnSrcSpan srcSpan) $ Ghc.Qual plutusTx occ)
            )

      tys =
        Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
          Ghc.DctMulti
            Ghc.noExtField
            [ mkCls (Ghc.mkClsOcc "ToData")
            , mkCls (Ghc.mkClsOcc "FromData")
            , mkCls (Ghc.mkClsOcc "UnsafeFromData")
            ]
   in Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
        Ghc.HsDerivingClause Ghc.noAnn (Just strategy) tys

-- | Build @{\-# COMPLETE Ex1, Ex2 #-\}@.
makeCompleteDecl
  :: Ghc.SrcSpan
  -> [Constructor.Constructor]
  -> Ghc.LHsDecl Ghc.GhcPs
makeCompleteDecl srcSpan constructors =
  let conNames =
        fmap
          (Ghc.L (Ghc.noAnnSrcSpan srcSpan) . Ghc.mkRdrUnqual . Ghc.rdrNameOcc . Constructor.name)
          constructors
   in Ghc.noLocA . Ghc.SigD Ghc.noExtField $ mkCompleteMatchSig srcSpan conNames

{-| Build a 'Ghc.CompleteMatchSig'. CPP-shimmed because both the annotation
payload and the conNames carrier changed in GHC 9.10. -}
mkCompleteMatchSig
  :: Ghc.SrcSpan
  -> [Ghc.LIdP Ghc.GhcPs]
  -> Ghc.Sig Ghc.GhcPs
#if __GLASGOW_HASKELL__ >= 910
mkCompleteMatchSig _ conNames =
  Ghc.CompleteMatchSig ((Ghc.noAnn, Nothing, Ghc.noAnn), Ghc.NoSourceText) conNames Nothing
#else
mkCompleteMatchSig srcSpan conNames =
  Ghc.CompleteMatchSig (Ghc.noAnn, Ghc.NoSourceText) (Ghc.L srcSpan conNames) Nothing
#endif

-- | Generate the bidirectional pattern synonym for one constructor.
makePatSynDecl
  :: Ghc.SrcSpan
  -> Type.Type
  -> Constructor.Constructor
  -> Integer
  -> Ghc.ModuleName
  -> Ghc.ModuleName
  -> Ghc.Hsc [Ghc.LHsDecl Ghc.GhcPs]
makePatSynDecl srcSpan type_ constructor idx plutusTx plutusTxBuiltins = do
  let fields = Constructor.fields constructor

  vars <- mapM (\_ -> Common.makeRandomVariable srcSpan "x_") fields
  dVar <- Common.makeRandomVariable srcSpan "d_"
  tagVar <- Common.makeRandomVariable srcSpan "tag_"
  argsVar <- Common.makeRandomVariable srcSpan "args_"
  viewVars <- mapM (\_ -> Common.makeRandomVariable srcSpan "a_") fields

  let conRdrName = Constructor.name constructor
      lConName = Ghc.L (Ghc.noAnnSrcSpan srcSpan) $ Ghc.mkRdrUnqual (Ghc.rdrNameOcc conRdrName)
      internalCon = Ghc.L (Ghc.noAnnSrcSpan srcSpan) $ Ghc.mkRdrUnqual (internalConName type_)

      -- The "where" (builder) body:
      -- Example_BD (mkConstr idx [toBuiltinData (x0_ :: T0), ...])
      encodeArgs =
        fmap
          ( \(v, field) ->
              Hs.app
                srcSpan
                (Hs.qualVar srcSpan plutusTx (Ghc.mkVarOcc "toBuiltinData"))
                -- type annotation so GHC can resolve ToData instance
                (Hs.par srcSpan $ typeAnnotate srcSpan (Field.type_ field) (Hs.var srcSpan v))
          )
          (zip vars fields)

      builderBody =
        Hs.app
          srcSpan
          ( Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
              Ghc.HsVar Ghc.noExtField internalCon
          )
          ( Hs.par srcSpan $
              Hs.app
                srcSpan
                ( Hs.app
                    srcSpan
                    (Hs.qualVar srcSpan plutusTxBuiltins (Ghc.mkVarOcc "mkConstr"))
                    (intLit srcSpan idx)
                )
                (Hs.explicitList srcSpan encodeArgs)
          )

      -- The match (destructor) pattern uses a view pattern:
      -- Example_BD (viewFn -> matchPat)
      viewFn = makeViewFn srcSpan fields idx dVar tagVar argsVar viewVars plutusTx plutusTxBuiltins
      matchPat = makeMatchPat srcSpan vars

      matchPat' =
        Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
          Ghc.ConPat
            Ghc.noAnn
            internalCon
            ( Ghc.PrefixCon
                []
                [ Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
                    Ghc.ViewPat Ghc.noAnn viewFn matchPat
                ]
            )

      -- pattern synonym args
      patArgs = Ghc.PrefixCon [] vars

      -- The explicit bidirectional direction
      builderMatch =
        Hs.funMatch
          srcSpan
          lConName
          (fmap (Hs.varPat srcSpan) vars)
          (Common.makeGRHSs srcSpan builderBody)

      patSynBind =
        Ghc.PatSynBind Ghc.noExtField $
          Ghc.PSB
            { Ghc.psb_ext = Ghc.noAnn
            , Ghc.psb_id = lConName
            , Ghc.psb_args = patArgs
            , Ghc.psb_def = matchPat'
            , Ghc.psb_dir =
                Ghc.ExplicitBidirectional $
                  Hs.mg (Ghc.L srcSpan [builderMatch])
            }

      patSynDecl = Ghc.noLocA $ Ghc.ValD Ghc.noExtField patSynBind

      -- The top-level signature: @pattern Con :: t0 -> ... -> tn -> T a b ...@
      tv :: Ghc.IdP Ghc.GhcPs -> Ghc.LHsType Ghc.GhcPs
      tv n = Hs.tyVar srcSpan (Ghc.L (Ghc.noAnnSrcSpan srcSpan) n)

      resultTy :: Ghc.LHsType Ghc.GhcPs
      resultTy =
        foldl
          (\acc v -> Ghc.L (Ghc.noAnnSrcSpan srcSpan) (Ghc.HsAppTy Ghc.noExtField acc (tv v)))
          (tv (Type.name type_))
          (Type.variables type_)

      patSynTy :: Ghc.LHsType Ghc.GhcPs
      patSynTy =
        foldr
          (\f acc -> Hs.funTy srcSpan (Ghc.L (Ghc.noAnnSrcSpan srcSpan) (Field.type_ f)) acc)
          resultTy
          fields
      sigDecl =
        Ghc.noLocA . Ghc.SigD Ghc.noExtField $
          Ghc.PatSynSig Ghc.noAnn [lConName] $
            Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
              Ghc.HsSig Ghc.noExtField Ghc.mkHsOuterImplicit patSynTy

  pure [sigDecl, patSynDecl]

-- | Wrap an expression with a type annotation: @(expr :: ty)@.
typeAnnotate
  :: Ghc.SrcSpan
  -> Ghc.HsType Ghc.GhcPs
  -> Ghc.LHsExpr Ghc.GhcPs
  -> Ghc.LHsExpr Ghc.GhcPs
typeAnnotate srcSpan ty expr =
  Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
    Ghc.ExprWithTySig
      Ghc.noAnn
      expr
      ( Ghc.HsWC Ghc.noExtField $
          Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
            Ghc.HsSig
              Ghc.noExtField
              Ghc.mkHsOuterImplicit
              (Ghc.L (Ghc.noAnnSrcSpan srcSpan) ty)
      )

{-| Build the view function for deconstruction.

Always checks the constructor tag; returns @Maybe@ so GHC can try the
next pattern alternative if the tag doesn't match:

@\d_ -> let tag_ = fst (unsafeDataAsConstr d_)
             args_ = snd (unsafeDataAsConstr d_)
         in if tag_ == idx then Just \<result\> else Nothing@

@\<result\>@ is @()@ for nullary constructors, @(x :: T)@ for arity-1,
or a tuple for higher arities. -}
makeViewFn
  :: Ghc.SrcSpan
  -> [Field.Field]
  -> Integer
  -> Ghc.LIdP Ghc.GhcPs
  -> Ghc.LIdP Ghc.GhcPs
  -> Ghc.LIdP Ghc.GhcPs
  -> [Ghc.LIdP Ghc.GhcPs]
  -> Ghc.ModuleName
  -> Ghc.ModuleName
  -> Ghc.LHsExpr Ghc.GhcPs
makeViewFn srcSpan fields idx dVar tagVar argsVar viewVars plutusTx plutusTxBuiltins =
  let ptx :: Ghc.OccName -> Ghc.LHsExpr Ghc.GhcPs
      ptx = Hs.qualVar srcSpan plutusTx

      blt :: Ghc.OccName -> Ghc.LHsExpr Ghc.GhcPs
      blt = Hs.qualVar srcSpan plutusTxBuiltins

      arity :: Int
      arity = length fields

      -- fst / snd (unsafeDataAsConstr d_)
      constrExpr =
        Hs.app
          srcSpan
          (blt (Ghc.mkVarOcc "unsafeDataAsConstr"))
          (Hs.var srcSpan dVar)

      getFst =
        Hs.app srcSpan (Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkVarOcc "fst"))) (Hs.par srcSpan constrExpr)
      getSnd =
        Hs.app srcSpan (Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkVarOcc "snd"))) (Hs.par srcSpan constrExpr)

      -- helper: 0-arg let binding  var = rhs
      mkLetFun :: Ghc.LIdP Ghc.GhcPs -> Ghc.LHsExpr Ghc.GhcPs -> Ghc.LHsBind Ghc.GhcPs
      mkLetFun var rhs =
        Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
          Ghc.FunBind
            Ghc.noExtField
            var
            (Hs.mg (Ghc.L srcSpan [Hs.funMatch srcSpan var [] (Common.makeGRHSs srcSpan rhs)]))

      tagBind = mkLetFun tagVar getFst
      argsBind = mkLetFun argsVar getSnd

      -- (unsafeFromBuiltinData e) :: fieldType
      decode :: Ghc.HsType Ghc.GhcPs -> Ghc.LHsExpr Ghc.GhcPs -> Ghc.LHsExpr Ghc.GhcPs
      decode fieldType e =
        typeAnnotate srcSpan fieldType $
          Hs.app
            srcSpan
            (ptx (Ghc.mkVarOcc "unsafeFromBuiltinData"))
            (Hs.par srcSpan e)

      -- The decoded fields, sourced from the explicitly bound @viewVars@.
      decoded = case zip viewVars fields of
        [(v, f)] -> decode (Field.type_ f) (Hs.var srcSpan v)
        vfs ->
          Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
            Ghc.ExplicitTuple
              Ghc.noAnn
              (fmap (\(v, f) -> Hs.tupArg (decode (Field.type_ f) (Hs.var srcSpan v))) vfs)
              Ghc.Boxed

      justDecoded =
        Hs.app
          srcSpan
          (Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkDataOcc "Just")))
          (Hs.par srcSpan decoded)

      nothingExpr =
        Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkDataOcc "Nothing"))

      -- case args_ of { [a0, ...] -> Just <decoded>; _ -> Nothing }
      argsListPat =
        Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
          Ghc.ListPat Ghc.noAnn (fmap (Hs.varPat srcSpan) viewVars)
      wildPat = Ghc.L (Ghc.noAnnSrcSpan srcSpan) (Ghc.WildPat Ghc.noExtField)
      argsCase =
        Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
          Ghc.HsCase Ghc.noAnn (Hs.var srcSpan argsVar) $
            Hs.mg $
              Ghc.L
                srcSpan
                [ Hs.caseMatch srcSpan [argsListPat] (Common.makeGRHSs srcSpan justDecoded)
                , Hs.caseMatch srcSpan [wildPat] (Common.makeGRHSs srcSpan nothingExpr)
                ]

      -- nullary: @Just ()@; otherwise the explicit-match case above
      thenExpr =
        if arity == 0
          then
            Hs.app
              srcSpan
              (Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkDataOcc "Just")))
              ( Hs.par srcSpan $
                  Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
                    Ghc.ExplicitTuple Ghc.noAnn [] Ghc.Boxed
              )
          else argsCase

      -- tagVar == idx
      cond =
        Hs.opApp
          srcSpan
          (Hs.var srcSpan tagVar)
          (Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkVarOcc "==")))
          (intLit srcSpan idx)

      ifExpr =
        Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
          Ghc.HsIf Ghc.noAnn cond thenExpr nothingExpr

      -- omit argsBind for nullary constructors (avoid unused-variable warning)
      letBinds = if arity == 0 then [tagBind] else [tagBind, argsBind]

      body =
        Hs.letE srcSpan (Hs.valLocalBinds letBinds) ifExpr
   in Hs.lam srcSpan . Hs.mg $
        Ghc.L
          srcSpan
          [ Hs.match
              srcSpan
              [Hs.varPat srcSpan dVar]
              (Common.makeGRHSs srcSpan body)
          ]

{-| Build the match pattern for the view result.
Always wrapped in @Just@: nullary → @Just ()@, arity 1 → @Just x0_@,
arity n → @Just (x0_, x1_, ...)@ -}
makeMatchPat
  :: Ghc.SrcSpan
  -> [Ghc.LIdP Ghc.GhcPs]
  -> Ghc.LPat Ghc.GhcPs
makeMatchPat srcSpan vars =
  let inner = case vars of
        [] ->
          Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
            Ghc.TuplePat Ghc.noAnn [] Ghc.Boxed
        [v] ->
          Hs.varPat srcSpan v
        _ ->
          Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
            Ghc.TuplePat Ghc.noAnn (fmap (Hs.varPat srcSpan) vars) Ghc.Boxed
   in Ghc.L (Ghc.noAnnSrcSpan srcSpan) $
        Ghc.ConPat
          Ghc.noAnn
          (Ghc.L (Ghc.noAnnSrcSpan srcSpan) (Ghc.mkRdrUnqual (Ghc.mkDataOcc "Just")))
          (Ghc.PrefixCon [] [inner])

-- | Rebuild 'LHsQTyVars' from the type variable 'RdrName's.
mkTyVars :: Ghc.SrcSpan -> [Ghc.IdP Ghc.GhcPs] -> Ghc.LHsQTyVars Ghc.GhcPs
mkTyVars srcSpan vars =
  Ghc.HsQTvs Ghc.noExtField (fmap (Hs.userTyVar srcSpan) vars)

-- | Integer overloaded literal.
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
