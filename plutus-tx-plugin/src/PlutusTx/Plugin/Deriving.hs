{-# LANGUAGE LambdaCase #-}

{-| The Plinth @deriving via@ pass. This is /not/ a standalone plugin: it is
wired into 'Plinth.Plugin.plugin' as its @parsedResultAction@, so that any
module compiled with the Plinth plugin can write

> data Shape = Point | Circle Integer Integer
>   deriving AsData via Plinth
>   deriving Optics via Plinth

without enabling a second plugin. -}
module PlutusTx.Plugin.Deriving
  ( parsedResultAction
  )
where

import Control.Monad qualified as Monad
import Control.Monad.IO.Class qualified as IO
import Data.Bifunctor
import Data.Foldable (for_)
import Data.Functor ((<&>))
import Data.List qualified as List
import Data.Maybe qualified as Maybe
import Data.Traversable (for)
import GHC.Hs qualified as Ghc
import GHC.Plugins qualified as Ghc
import PlutusTx.Plugin.Deriving.Generator.AsData qualified as AsData
import PlutusTx.Plugin.Deriving.Generator.Common qualified as Common
import PlutusTx.Plugin.Deriving.Generator.Match qualified as Match
import PlutusTx.Plugin.Deriving.Generator.Optics qualified as Optics
import PlutusTx.Plugin.Deriving.Hs (pattern Loc)
import PlutusTx.Plugin.Deriving.Hsc qualified as Hsc

{-| The @parsedResultAction@ hook: rewrite @deriving … via Plinth@ clauses in
the freshly-parsed module into the generated declarations. -}
parsedResultAction
  :: [Ghc.CommandLineOption]
  -> Ghc.ModSummary
  -> Ghc.ParsedResult
  -> Ghc.Hsc Ghc.ParsedResult
parsedResultAction _commandLineOptions modSummary (Ghc.ParsedResult hsParsedModule msgs) = do
  let moduleName = Ghc.moduleName $ Ghc.ms_mod modSummary
  lHsModule2 <- handleLHsModule moduleName (Ghc.hpm_module hsParsedModule)
  pure $ Ghc.ParsedResult hsParsedModule {Ghc.hpm_module = lHsModule2} msgs

type LHsModule = Ghc.Located (Ghc.HsModule Ghc.GhcPs)

handleLHsModule
  :: Ghc.ModuleName
  -> LHsModule
  -> Ghc.Hsc LHsModule
handleLHsModule moduleName lHsModule = do
  hsModule <- handleHsModule moduleName $ Ghc.unLoc lHsModule
  pure $ Ghc.L (Ghc.getLoc lHsModule) hsModule

handleHsModule
  :: Ghc.ModuleName
  -> Ghc.HsModule Ghc.GhcPs
  -> Ghc.Hsc (Ghc.HsModule Ghc.GhcPs)
handleHsModule moduleName hsModule = do
  (lImportDecls, lHsDecls) <-
    handleLHsDecls moduleName $
      Ghc.hsmodDecls hsModule
  pure
    hsModule
      { Ghc.hsmodImports = Ghc.hsmodImports hsModule <> lImportDecls
      , Ghc.hsmodDecls = lHsDecls
      }

handleLHsDecls
  :: Ghc.ModuleName
  -> [Ghc.LHsDecl Ghc.GhcPs]
  -> Ghc.Hsc ([Ghc.LImportDecl Ghc.GhcPs], [Ghc.LHsDecl Ghc.GhcPs])
handleLHsDecls moduleName lHsDecls = do
  tuples <- for lHsDecls (handleLHsDecl moduleName)
  pure (bimap mconcat mconcat $ unzip tuples)

handleLHsDecl
  :: Ghc.ModuleName
  -> Ghc.LHsDecl Ghc.GhcPs
  -> Ghc.Hsc ([Ghc.LImportDecl Ghc.GhcPs], [Ghc.LHsDecl Ghc.GhcPs])
handleLHsDecl moduleName lHsDecl = case Ghc.unLoc lHsDecl of
  Ghc.TyClD xTyClD tyClDecl1 -> do
    (mTyClDecl2, (lImportDecls, lHsDecls)) <- handleTyClDecl moduleName tyClDecl1
    case mTyClDecl2 of
      Nothing ->
        pure (lImportDecls, lHsDecls)
      Just tyClDecl2 ->
        let newDecl = Ghc.L (Ghc.getLoc lHsDecl) (Ghc.TyClD xTyClD tyClDecl2)
         in pure (lImportDecls, newDecl : lHsDecls)
  _ -> pure ([], [lHsDecl])

handleTyClDecl
  :: Ghc.ModuleName
  -> Ghc.TyClDecl Ghc.GhcPs
  -> Ghc.Hsc
       ( Maybe (Ghc.TyClDecl Ghc.GhcPs)
       , ([Ghc.LImportDecl Ghc.GhcPs], [Ghc.LHsDecl Ghc.GhcPs])
       )
handleTyClDecl moduleName tyClDecl = case tyClDecl of
  d@Ghc.DataDecl {} -> do
    (mHsDataDefn, extras) <-
      handleHsDataDefn moduleName (Ghc.tcdLName d) (Ghc.tcdTyVars d) (Ghc.tcdDataDefn d)
    pure (mHsDataDefn <&> \defn -> d {Ghc.tcdDataDefn = defn}, extras)
  _ -> pure (Just tyClDecl, ([], []))

handleHsDataDefn
  :: Ghc.ModuleName
  -> Ghc.LIdP Ghc.GhcPs
  -> Ghc.LHsQTyVars Ghc.GhcPs
  -> Ghc.HsDataDefn Ghc.GhcPs
  -> Ghc.Hsc
       ( Maybe (Ghc.HsDataDefn Ghc.GhcPs)
       , ([Ghc.LImportDecl Ghc.GhcPs], [Ghc.LHsDecl Ghc.GhcPs])
       )
handleHsDataDefn moduleName lIdP lHsQTyVars hsDataDefn = do
  let consList = case Ghc.dd_cons hsDataDefn of
        Ghc.DataTypeCons _ cs -> cs
        Ghc.NewTypeCon c -> [c]
  (mHsDeriving, extras) <-
    handleHsDeriving moduleName lIdP lHsQTyVars consList (Ghc.dd_derivs hsDataDefn)
  pure (mHsDeriving <&> \d -> hsDataDefn {Ghc.dd_derivs = d}, extras)

handleHsDeriving
  :: Ghc.ModuleName
  -> Ghc.LIdP Ghc.GhcPs
  -> Ghc.LHsQTyVars Ghc.GhcPs
  -> [Ghc.LConDecl Ghc.GhcPs]
  -> Ghc.HsDeriving Ghc.GhcPs
  -> Ghc.Hsc
       ( Maybe (Ghc.HsDeriving Ghc.GhcPs)
       , ( [Ghc.LImportDecl Ghc.GhcPs]
         , [Ghc.LHsDecl Ghc.GhcPs]
         )
       )
handleHsDeriving moduleName lIdP lHsQTyVars lConDecls hsDeriving = do
  (dropOriginal, lHsDerivingClauses, (lImportDecls, lHsDecls)) <-
    handleLHsDerivingClauses moduleName lIdP lHsQTyVars lConDecls hsDeriving
  pure
    ( if dropOriginal then Nothing else Just lHsDerivingClauses
    , (lImportDecls, lHsDecls)
    )

handleLHsDerivingClauses
  :: Ghc.ModuleName
  -> Ghc.LIdP Ghc.GhcPs
  -> Ghc.LHsQTyVars Ghc.GhcPs
  -> [Ghc.LConDecl Ghc.GhcPs]
  -> Ghc.HsDeriving Ghc.GhcPs
  -> Ghc.Hsc
       ( Bool
       , [Ghc.LHsDerivingClause Ghc.GhcPs]
       , ( [Ghc.LImportDecl Ghc.GhcPs]
         , [Ghc.LHsDecl Ghc.GhcPs]
         )
       )
handleLHsDerivingClauses moduleName lIdP lHsQTyVars lConDecls lHsDerivingClauses = do
  tuples <-
    for
      lHsDerivingClauses
      (handleLHsDerivingClause moduleName lIdP lHsQTyVars lConDecls lHsDerivingClauses)

  let mClauses :: [Maybe (Ghc.LHsDerivingClause Ghc.GhcPs)]
      dropFlags :: [Bool]
      extras :: [([Ghc.LImportDecl Ghc.GhcPs], [Ghc.LHsDecl Ghc.GhcPs])]
      (mClauses, dropFlags, extras) = unzip3 tuples
      (dropped, kept) = List.partition fst (zip dropFlags extras)
      orderedExtras = fmap snd dropped <> fmap snd kept
  pure
    ( or dropFlags
    , Maybe.catMaybes mClauses
    , bimap mconcat mconcat $ unzip orderedExtras
    )

handleLHsDerivingClause
  :: Ghc.ModuleName
  -> Ghc.LIdP Ghc.GhcPs
  -> Ghc.LHsQTyVars Ghc.GhcPs
  -> [Ghc.LConDecl Ghc.GhcPs]
  -> Ghc.HsDeriving Ghc.GhcPs
  -> Ghc.LHsDerivingClause Ghc.GhcPs
  -> Ghc.Hsc
       ( Maybe (Ghc.LHsDerivingClause Ghc.GhcPs)
       , Bool
       , ( [Ghc.LImportDecl Ghc.GhcPs]
         , [Ghc.LHsDecl Ghc.GhcPs]
         )
       )
handleLHsDerivingClause moduleName lIdP lHsQTyVars lConDecls lHsDerivingClauses lHsDerivingClause =
  case Ghc.unLoc lHsDerivingClause of
    Ghc.HsDerivingClause _ deriv_clause_strategy deriv_clause_tys
      | Common.isPlinthVia deriv_clause_strategy -> do
          let nonPlinthClauses =
                filter
                  ( \c -> case Ghc.unLoc c of
                      Ghc.HsDerivingClause _ s _ ->
                        not (Common.isPlinthVia s)
                  )
                  lHsDerivingClauses
          (dropOriginal, lImportDecls, lHsDecls) <-
            handleLHsSigTypes moduleName lIdP lHsQTyVars lConDecls nonPlinthClauses
              . toLHsSigTypes
              $ Ghc.unLoc deriv_clause_tys
          pure (Nothing, dropOriginal, (lImportDecls, lHsDecls))
    _ -> pure (Just lHsDerivingClause, False, ([], []))

toLHsSigTypes :: Ghc.DerivClauseTys Ghc.GhcPs -> [Ghc.LHsSigType Ghc.GhcPs]
toLHsSigTypes = \case
  Ghc.DctSingle _ lHsSigType -> [lHsSigType]
  Ghc.DctMulti _ lHsSigTypes -> lHsSigTypes

handleLHsSigTypes
  :: Ghc.ModuleName
  -> Ghc.LIdP Ghc.GhcPs
  -> Ghc.LHsQTyVars Ghc.GhcPs
  -> [Ghc.LConDecl Ghc.GhcPs]
  -> Ghc.HsDeriving Ghc.GhcPs
  -> [Ghc.LHsSigType Ghc.GhcPs]
  -> Ghc.Hsc
       ( Bool
       , [Ghc.LImportDecl Ghc.GhcPs]
       , [Ghc.LHsDecl Ghc.GhcPs]
       )
handleLHsSigTypes moduleName lIdP lHsQTyVars lConDecls lHsDerivingClauses lHsSigTypes = do
  tuples <-
    for
      lHsSigTypes
      (handleLHsSigType moduleName lIdP lHsQTyVars lConDecls lHsDerivingClauses)
  let (dropFlags, importLists, declLists) = unzip3 tuples
  pure (or dropFlags, mconcat importLists, mconcat declLists)

handleLHsSigType
  :: Ghc.ModuleName
  -> Ghc.LIdP Ghc.GhcPs
  -> Ghc.LHsQTyVars Ghc.GhcPs
  -> [Ghc.LConDecl Ghc.GhcPs]
  -> Ghc.HsDeriving Ghc.GhcPs
  -> Ghc.LHsSigType Ghc.GhcPs
  -> Ghc.Hsc
       ( Bool
       , [Ghc.LImportDecl Ghc.GhcPs]
       , [Ghc.LHsDecl Ghc.GhcPs]
       )
handleLHsSigType moduleName lIdP lHsQTyVars lConDecls lHsDerivingClauses lHsSigType =
  do
    let srcSpan = Ghc.getLocA lHsSigType
    (dropOriginal, lImportDecls, lHsDecls) <- case getGenerator lHsSigType of
      Just generate ->
        generate lHsDerivingClauses moduleName lIdP lHsQTyVars lConDecls srcSpan
      Nothing -> Hsc.throwError srcSpan $ Ghc.text "unsupported type class"

    verbose <- isVerbose
    Monad.when verbose do
      IO.liftIO do
        putStrLn $ replicate 80 '-'
        for_ lImportDecls (putStrLn . Ghc.showPprUnsafe . Ghc.ppr)
        for_ lHsDecls (putStrLn . Ghc.showPprUnsafe . Ghc.ppr)

    pure (dropOriginal, lImportDecls, lHsDecls)

-- | Whether to dump the generated declarations, driven by @-ddump-deriv@.
isVerbose :: Ghc.Hsc Bool
isVerbose =
  Ghc.dopt Ghc.Opt_D_dump_deriv <$> Ghc.getDynFlags

getGenerator :: Ghc.LHsSigType Ghc.GhcPs -> Maybe (Ghc.HsDeriving Ghc.GhcPs -> Common.Generator)
getGenerator lHsSigType = do
  className <- getClassName lHsSigType
  lookup className generators

generators :: [(String, Ghc.HsDeriving Ghc.GhcPs -> Common.Generator)]
generators =
  [ ("AsData", AsData.generate)
  , ("Match", Match.generate)
  , ("Optics", Optics.generate)
  ]

getClassName :: Ghc.LHsSigType Ghc.GhcPs -> Maybe String
getClassName (Loc lHsSigType)
  | Ghc.HsSig _ _ (Loc lHsType) <- lHsSigType
  , Ghc.HsTyVar _ _ (Loc lIdP) <- lHsType
  , Ghc.Unqual x <- lIdP =
      Just $ Ghc.occNameString x
  | otherwise =
      Nothing
