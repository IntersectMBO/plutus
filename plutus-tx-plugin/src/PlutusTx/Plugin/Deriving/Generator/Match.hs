{-# LANGUAGE LambdaCase #-}

module PlutusTx.Plugin.Deriving.Generator.Match
  ( generate
  )
where

import Control.Monad (when)
import Data.List qualified as List
import Data.Traversable (for)
import GHC.Hs qualified as Ghc
import GHC.Plugins qualified as Ghc
import PlutusTx.Plugin.Deriving.Constant.Module qualified as Module
import PlutusTx.Plugin.Deriving.Generator.Common qualified as Common
import PlutusTx.Plugin.Deriving.Hs (loc, pattern Loc)
import PlutusTx.Plugin.Deriving.Hs qualified as Hs
import PlutusTx.Plugin.Deriving.Hsc qualified as Hsc
import PlutusTx.Plugin.Deriving.Type.Constructor qualified as Constructor
import PlutusTx.Plugin.Deriving.Type.Field qualified as Field
import PlutusTx.Plugin.Deriving.Type.Type qualified as Type

{-| Generates a CPS-style destructor function for 'AsData' sum types.

Given:

> data Example a = Ex1 Integer | Ex2 a a
>   deriving (AsData, Match) via Plinth

Generates:

> matchExample :: Example a -> (Integer -> r_N) -> (a -> a -> r_N) -> r_N
> matchExample (Example_BD d_) f_0 f_1 =
>   let tag_ = fst (PlutusTx.Builtins.unsafeDataAsConstr d_)
>       args_ = snd (PlutusTx.Builtins.unsafeDataAsConstr d_)
>   in if tag_ == 0
>      then f_0 ((PlutusTx.unsafeFromBuiltinData (head args_)) :: Integer)
>      else f_1 ((PlutusTx.unsafeFromBuiltinData (head args_)) :: a)
>               ((PlutusTx.unsafeFromBuiltinData (head (tail args_))) :: a)

For a single-constructor type, the tag check is omitted entirely:

> data Address = Address Credential (Maybe StakingCredential)
>   deriving (AsData, Match) via Plinth

Generates:

> matchAddress :: Address -> (Credential -> Maybe StakingCredential -> r_N) -> r_N
> matchAddress (Address_BD d_) f_ =
>   let args_ = snd (PlutusTx.Builtins.unsafeDataAsConstr d_)
>   in f_ ((PlutusTx.unsafeFromBuiltinData (head args_)) :: Credential)
>          ((PlutusTx.unsafeFromBuiltinData (head (tail args_))) :: Maybe StakingCredential) -}
generate :: Ghc.HsDeriving Ghc.GhcPs -> Common.Generator
generate _ _moduleName lIdP lHsQTyVars lConDecls srcSpan = do
  type_ <- Type.make lIdP lHsQTyVars lConDecls srcSpan
  let
    constructors :: [Constructor.Constructor]
    constructors = Type.constructors type_
  when (null constructors) $
    Hsc.throwError srcSpan $
      Ghc.text "Match requires at least one constructor"

  plutusTx <- Common.makeRandomModule Module.plutusTx
  plutusTxBuiltins <- Common.makeRandomModule Module.plutusTxBuiltins

  let
    lImportDecls :: [Ghc.LImportDecl Ghc.GhcPs]
    lImportDecls =
      Hs.importDecls
        srcSpan
        [ (Module.plutusTx, plutusTx)
        , (Module.plutusTxBuiltins, plutusTxBuiltins)
        ]

  decls <- makeMatchDecls srcSpan type_ constructors plutusTx plutusTxBuiltins
  pure (False, lImportDecls, decls)

-- | The internal BD constructor name (same convention as 'AsData').
internalConName :: Type.Type -> Ghc.OccName
internalConName type_ =
  Ghc.mkDataOcc $
    Ghc.occNameString (Ghc.rdrNameOcc (Type.name type_)) <> "_BD"

-- | @"match" <> TypeName@, e.g. @matchExample@.
matchFunOcc :: Type.Type -> Ghc.OccName
matchFunOcc type_ =
  Ghc.mkVarOcc $
    "match" <> Ghc.occNameString (Ghc.rdrNameOcc (Type.name type_))

makeMatchDecls
  :: Ghc.SrcSpan
  -> Type.Type
  -> [Constructor.Constructor]
  -> Ghc.ModuleName
  -> Ghc.ModuleName
  -> Ghc.Hsc [Ghc.LHsDecl Ghc.GhcPs]
makeMatchDecls srcSpan type_ constructors plutusTx plutusTxBuiltins = do
  let
    funOcc :: Ghc.OccName
    funOcc = matchFunOcc type_

    funId :: Ghc.LIdP Ghc.GhcPs
    funId = loc srcSpan (Ghc.Unqual funOcc)

    internalCon :: Ghc.LIdP Ghc.GhcPs
    internalCon =
      loc srcSpan do
        Ghc.mkRdrUnqual (internalConName type_)

  dVar <- Common.makeRandomVariable srcSpan "d_"
  tagVar <- Common.makeRandomVariable srcSpan "tag_"
  argsVar <- Common.makeRandomVariable srcSpan "args_"
  contVars <- for constructors \_ -> Common.makeRandomVariable srcSpan "f_"
  fieldVarss <-
    for constructors \constructor ->
      for (Constructor.fields constructor) \_ ->
        Common.makeRandomVariable srcSpan "a_"

  rVar <- Common.makeRandomVariable srcSpan "r_"

  let
    sigDecl :: Ghc.LHsDecl Ghc.GhcPs
    sigDecl = makeSigDecl srcSpan type_ constructors funId rVar

    valDecl :: Ghc.LHsDecl Ghc.GhcPs
    valDecl =
      makeValDecl
        srcSpan
        constructors
        funOcc
        dVar
        tagVar
        argsVar
        internalCon
        contVars
        fieldVarss
        plutusTx
        plutusTxBuiltins

  pure [sigDecl, valDecl]

{-| Build the type signature.

@matchExample :: Example a -> (Integer -> r_N) -> (a -> a -> r_N) -> r_N@ -}
makeSigDecl
  :: Ghc.SrcSpan
  -> Type.Type
  -> [Constructor.Constructor]
  -> Ghc.LIdP Ghc.GhcPs
  -> Ghc.LIdP Ghc.GhcPs
  -> Ghc.LHsDecl Ghc.GhcPs
makeSigDecl srcSpan type_ constructors funId (Loc rVar) =
  Ghc.noLocA $
    Ghc.SigD Ghc.noExtField $
      Ghc.TypeSig Ghc.noAnn [funId] $
        Ghc.HsWC Ghc.noExtField $
          loc srcSpan do
            Ghc.HsSig Ghc.noExtField Ghc.mkHsOuterImplicit fullTy
  where
    -- @rVar@ is made in the value namespace; as the result /type/ variable
    -- it must be in the type-variable namespace, else implicit
    -- quantification does not bind it ("not in scope").
    rTyName :: Ghc.LIdP Ghc.GhcPs
    rTyName =
      loc srcSpan do
        Ghc.mkRdrUnqual (Ghc.mkTyVarOcc (Ghc.occNameString (Ghc.rdrNameOcc rVar)))

    rTy :: Ghc.LHsType Ghc.GhcPs
    rTy =
      loc srcSpan do
        Ghc.HsTyVar Ghc.noAnn Ghc.NotPromoted rTyName

    -- A -> B -> ... -> r  for a constructor's fields
    mkContTy :: [Field.Field] -> Ghc.LHsType Ghc.GhcPs
    mkContTy fields =
      foldr
        (Hs.funTy srcSpan . loc srcSpan . Field.type_)
        rTy
        fields

    -- Wrap in parens unless nullary (just r)
    mkContTyPar :: [Field.Field] -> Ghc.LHsType Ghc.GhcPs
    mkContTyPar = \case
      [] -> rTy
      fields -> loc srcSpan $ Ghc.HsParTy Ghc.noAnn (mkContTy fields)

    outerTy :: Ghc.LHsType Ghc.GhcPs
    outerTy = mkOuterTy srcSpan type_

    contTys :: [Ghc.LHsType Ghc.GhcPs]
    contTys = fmap (mkContTyPar . Constructor.fields) constructors

    -- TypeName vars -> cont0 -> ... -> r
    fullTy :: Ghc.LHsType Ghc.GhcPs
    fullTy =
      foldr
        (Hs.funTy srcSpan)
        rTy
        (outerTy : contTys)

-- | @TypeName a b ...@ as an 'LHsType', parenthesised when there are type vars.
mkOuterTy :: Ghc.SrcSpan -> Type.Type -> Ghc.LHsType Ghc.GhcPs
mkOuterTy srcSpan type_ =
  case Type.variables type_ of
    [] -> applied
    _ -> loc srcSpan $ Ghc.HsParTy Ghc.noAnn applied
  where
    -- Fresh location wrappers per position (a shared @loc@ monomorphises
    -- to the wrong annotation type under GHC ≥ 9.10).
    tv :: Ghc.IdP Ghc.GhcPs -> Ghc.LHsType Ghc.GhcPs
    tv n = Hs.tyVar srcSpan (loc srcSpan n)

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

-- | Build the function value declaration.
makeValDecl
  :: Ghc.SrcSpan
  -> [Constructor.Constructor]
  -> Ghc.OccName
  -> Ghc.LIdP Ghc.GhcPs
  -> Ghc.LIdP Ghc.GhcPs
  -> Ghc.LIdP Ghc.GhcPs
  -> Ghc.LIdP Ghc.GhcPs
  -> [Ghc.LIdP Ghc.GhcPs]
  -> [[Ghc.LIdP Ghc.GhcPs]]
  -> Ghc.ModuleName
  -> Ghc.ModuleName
  -> Ghc.LHsDecl Ghc.GhcPs
makeValDecl srcSpan constructors funOcc dVar tagVar argsVar internalCon contVars fieldVarss plutusTx plutusTxBuiltins =
  Ghc.noLocA $
    Ghc.ValD Ghc.noExtField $
      Ghc.unLoc (Common.makeLHsBind srcSpan funOcc allPats body)
  where
    ptx :: Ghc.OccName -> Ghc.LHsExpr Ghc.GhcPs
    ptx = Hs.qualVar srcSpan plutusTx

    blt :: Ghc.OccName -> Ghc.LHsExpr Ghc.GhcPs
    blt = Hs.qualVar srcSpan plutusTxBuiltins

    -- (unsafeFromBuiltinData e) :: FieldType
    decode :: Field.Field -> Ghc.LHsExpr Ghc.GhcPs -> Ghc.LHsExpr Ghc.GhcPs
    decode field e =
      typeAnnotate srcSpan (Field.type_ field) $
        Hs.app
          srcSpan
          (ptx (Ghc.mkVarOcc "unsafeFromBuiltinData"))
          (Hs.par srcSpan e)

    unitExpr :: Ghc.LHsExpr Ghc.GhcPs
    unitExpr =
      loc srcSpan $ Ghc.ExplicitTuple Ghc.noAnn [] Ghc.Boxed

    -- Apply a continuation to the decoded fields, binding them with an
    -- explicit list pattern rather than head/tail:
    -- @case args_ of { [a0, ...] -> f_ (decode a0) ...; _ -> error () }@.
    -- The wildcard branch is unreachable for well-formed Data.
    applyFn
      :: Ghc.LIdP Ghc.GhcPs
      -> [Field.Field]
      -> [Ghc.LIdP Ghc.GhcPs]
      -> Ghc.LHsExpr Ghc.GhcPs
    applyFn fVar [] _fieldVars = Hs.var srcSpan fVar
    applyFn fVar fields fieldVars =
      loc srcSpan do
        Ghc.HsCase Ghc.noAnn (Hs.var srcSpan argsVar) $
          Hs.mg $
            Ghc.L
              srcSpan
              [ Hs.caseMatch srcSpan [listPat] (Common.makeGRHSs srcSpan applied)
              , Hs.caseMatch srcSpan [wildPat] (Common.makeGRHSs srcSpan errExpr)
              ]
      where
        applied :: Ghc.LHsExpr Ghc.GhcPs
        applied =
          List.foldl'
            (Hs.app srcSpan)
            (Hs.var srcSpan fVar)
            (zipWith (\f v -> decode f (Hs.var srcSpan v)) fields fieldVars)

        listPat :: Ghc.LPat Ghc.GhcPs
        listPat =
          loc srcSpan do
            Ghc.ListPat Ghc.noAnn (fmap (Hs.varPat srcSpan) fieldVars)

        wildPat :: Ghc.LPat Ghc.GhcPs
        wildPat = loc srcSpan (Ghc.WildPat Ghc.noExtField)

        errExpr :: Ghc.LHsExpr Ghc.GhcPs
        errExpr =
          Hs.app srcSpan (blt (Ghc.mkVarOcc "error")) (Hs.par srcSpan unitExpr)

    -- Nested if-else dispatch; last constructor falls through without a tag check
    makeDispatch
      :: [(Integer, Ghc.LIdP Ghc.GhcPs, Constructor.Constructor, [Ghc.LIdP Ghc.GhcPs])]
      -> Ghc.LHsExpr Ghc.GhcPs
    makeDispatch = \case
      [] -> error "Match.makeDispatch: empty list"
      [(_, fVar, con, fvs)] -> applyFn fVar (Constructor.fields con) fvs
      ((idx, fVar, con, fvs) : rest) ->
        loc srcSpan do
          Ghc.HsIf
            Ghc.noAnn
            ( Hs.opApp
                srcSpan
                (Hs.var srcSpan tagVar)
                (Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkVarOcc "==")))
                (intLit srcSpan idx)
            )
            (applyFn fVar (Constructor.fields con) fvs)
            (makeDispatch rest)

    needsTag :: Bool
    needsTag = length constructors > 1

    needsArgs :: Bool
    needsArgs = any (not . null . Constructor.fields) constructors

    constrExpr :: Ghc.LHsExpr Ghc.GhcPs
    constrExpr =
      Hs.app
        srcSpan
        (blt (Ghc.mkVarOcc "unsafeDataAsConstr"))
        (Hs.var srcSpan dVar)

    getFst :: Ghc.LHsExpr Ghc.GhcPs
    getFst =
      Hs.app srcSpan (Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkVarOcc "fst"))) (Hs.par srcSpan constrExpr)

    getSnd :: Ghc.LHsExpr Ghc.GhcPs
    getSnd =
      Hs.app srcSpan (Hs.var srcSpan (Hs.unqual srcSpan (Ghc.mkVarOcc "snd"))) (Hs.par srcSpan constrExpr)

    mkLetFun :: Ghc.LIdP Ghc.GhcPs -> Ghc.LHsExpr Ghc.GhcPs -> Ghc.LHsBind Ghc.GhcPs
    mkLetFun var rhs =
      loc srcSpan do
        Ghc.FunBind
          Ghc.noExtField
          var
          (Hs.mg (Ghc.L srcSpan [Hs.funMatch srcSpan var [] (Common.makeGRHSs srcSpan rhs)]))

    tagBind :: Ghc.LHsBind Ghc.GhcPs
    tagBind = mkLetFun tagVar getFst

    argsBind :: Ghc.LHsBind Ghc.GhcPs
    argsBind = mkLetFun argsVar getSnd

    letBinds :: [Ghc.LHsBind Ghc.GhcPs]
    letBinds =
      mconcat
        [ if needsTag then [tagBind] else []
        , if needsArgs then [argsBind] else []
        ]

    innerBody :: Ghc.LHsExpr Ghc.GhcPs
    innerBody
      | ([con], [cv], [fvs]) <- (constructors, contVars, fieldVarss) =
          applyFn cv (Constructor.fields con) fvs
      | otherwise =
          makeDispatch (List.zip4 [0 ..] contVars constructors fieldVarss)

    body :: Ghc.LHsExpr Ghc.GhcPs
    body
      | null letBinds =
          innerBody
      | otherwise =
          Hs.letE srcSpan (Hs.valLocalBinds letBinds) innerBody

    -- (TypeName_BD d_) or (TypeName_BD _) when d_ is unused
    innerPat :: Ghc.LPat Ghc.GhcPs
    innerPat
      | null letBinds =
          loc srcSpan $ Ghc.WildPat Ghc.noExtField
      | otherwise =
          Hs.varPat srcSpan dVar

    dPat :: Ghc.LPat Ghc.GhcPs
    dPat =
      loc srcSpan do
        Ghc.ConPat Ghc.noAnn internalCon (Ghc.PrefixCon [] [innerPat])

    allPats :: [Ghc.LPat Ghc.GhcPs]
    allPats = dPat : fmap (Hs.varPat srcSpan) contVars

-- | Wrap an expression with a type annotation: @(expr :: ty)@.
typeAnnotate
  :: Ghc.SrcSpan
  -> Ghc.HsType Ghc.GhcPs
  -> Ghc.LHsExpr Ghc.GhcPs
  -> Ghc.LHsExpr Ghc.GhcPs
typeAnnotate srcSpan ty expr =
  loc srcSpan do
    Ghc.ExprWithTySig Ghc.noAnn expr $
      Ghc.HsWC Ghc.noExtField $
        loc srcSpan do
          Ghc.HsSig
            Ghc.noExtField
            Ghc.mkHsOuterImplicit
            (loc srcSpan ty)

-- | Integer overloaded literal.
intLit :: Ghc.SrcSpan -> Integer -> Ghc.LHsExpr Ghc.GhcPs
intLit = Hs.intLit
