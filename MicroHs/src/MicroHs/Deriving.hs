module MicroHs.Deriving(deriveStrat, expandField, mkGetName, etaReduce) where
import Data.Char
import Data.Function
import Data.List
import Debug.Trace
import MHSPrelude
import MicroHs.Builtin
import MicroHs.Expr
import MicroHs.Ident
import MicroHs.IdentMap qualified as M
import MicroHs.List
import MicroHs.Names
import MicroHs.TCMonad
import Prelude qualified ()

-- Deriving runs when types level names are resolved, but not value level names.
-- To get access to names that might not be in scope, the module Mhs.Builtin
-- re-exports all names needed here.  This module is automagically imported as B@
-- Generated names should be like
--   type/class names fully qualified
--   method names (on lhs) unqualified
--   constructor names in the derived type unqualified
--   all other names should be qualified with B@

deriveStrat :: Maybe EConstraint -> Bool -> LHS -> [Constr] -> DerStrategy -> (Int, EConstraint) -> T [EDef]
deriveStrat mctx newt lhs cs strat (narg, cls) =  -- narg is the number of arguments that need eta reducing
--  trace ("deriveStrat " ++ show (mctx, newt, lhs, cs, strat, narg, cls)) $
  case strat of
    DerNone | newt && useNewt cls -> newtypeDer  mctx narg lhs (cs!!0) cls Nothing
            | otherwise           -> deriveNoHdr mctx narg lhs cs cls
    DerStock                      -> deriveNoHdr mctx narg lhs cs cls
    DerNewtype | newt             -> newtypeDer  mctx narg lhs (cs!!0) cls Nothing
    DerAnyClass                   -> anyclassDer mctx narg lhs cls
    DerVia via | newt             -> newtypeDer  mctx narg lhs (cs!!0) cls (Just via)
    _                             -> cannotDerive lhs cls
  where useNewt d = unIdent (getAppCon d) `notElem`
          ["Data.Data.Data", "Data.Typeable.Typeable", "GHC.Generics.Generic",
           "Language.Haskell.TH.Syntax.Lift", "Text.Read.Internal.Read", "Text.Show.Show"]

type DeriverT = Int -> LHS -> [Constr] -> EConstraint -> T [EDef]   -- Bool indicates a newtype
type Deriver = Maybe EConstraint -> DeriverT

derivers :: [(String, Deriver)]
derivers =
  [("Data.Bounded.Bounded",            derBounded)
  ,("Data.Enum_Class.Enum",            derEnum)
  ,("Data.Data.Data",                  derData)
  ,("Data.Eq.Eq",                      derEq)
  ,("Data.Functor.Functor",            derNotYet) -- derFunctor)
  ,("Data.Ix.Ix",                      derNotYet)
  ,("Data.Ord.Ord",                    derOrd)
  ,("Data.Typeable.Typeable",          derTypeable)
  ,("GHC.Generics.Generic",            derNotYet)
  ,("Language.Haskell.TH.Syntax.Lift", derLift)
  ,("Text.Read.Internal.Read",         derRead)
  ,("Text.Show.Show",                  derShow)
  ]

deriveNoHdr :: Maybe EConstraint -> DeriverT
deriveNoHdr mctx narg lhs cs d = do
--  traceM ("deriveNoHdr " ++ show d)
  case getDeriver d of
    Just f -> f mctx narg lhs cs d
    _      -> cannotDerive lhs d

getDeriver :: EConstraint -> Maybe Deriver
getDeriver d = lookup (unIdent $ getAppCon d) derivers

derNotYet :: Deriver
derNotYet _ _ _ _ d = do
  notYet d
  return []

notYet :: EConstraint -> T ()
notYet d =
  traceM ("Warning: cannot derive " ++ show d ++ " yet, " ++ showSLoc (getSLoc d))

-- We will never have Template Haskell, but we pretend we can derive Lift for it.
derLift :: Deriver
derLift _ _ _ _ _ = return []

--------------------------------------------

expandField :: EDef -> T [EDef]
expandField def@(Data    lhs cs _) = (++ [def]) <$> genHasFields lhs cs
expandField def@(Newtype lhs  c _) = (++ [def]) <$> genHasFields lhs [c]
expandField def                    = return [def]

genHasFields :: LHS -> [Constr] -> T [EDef]
genHasFields lhs cs = do
  let fldtys = nubBy ((==) `on` fst) [ (fld, ty) | Constr _ _ _ (Right fs) <- cs, (fld, (_, ty)) <- fs ]
--      flds = map fst fldtys
  concat <$> mapM (genHasField lhs cs) fldtys

genHasField :: LHS -> [Constr] -> (Ident, EType) -> T [EDef]
genHasField (tycon, iks) cs (fld, fldty) = do
  mn <- gets moduleName
  let loc = getSLoc tycon
      qtycon = qualIdent mn tycon
      eFld = EVar fld
      ufld = unIdent fld
      undef = mkExn loc ufld "recSelError"
      iHasField = mkIdentSLoc loc nameHasField
      iSetField = mkIdentSLoc loc nameSetField
      igetField = mkIdentSLoc loc namegetField
      isetField = mkIdentSLoc loc namesetField
      hdrGet = eForall iks $ eApp3 (EVar iHasField)
                                   (ELit loc (LStr ufld))
                                   (eApps (EVar qtycon) (map (EVar . idKindIdent) iks))
                                   fldty
      hdrSet = eForall iks $ eApp3 (EVar iSetField)
                                   (ELit loc (LStr ufld))
                                   (eApps (EVar qtycon) (map (EVar . idKindIdent) iks))
                                   fldty
      conEqnGet (Constr _ _ c (Left ts))   = eEqn [eApps (EVar c) (map (const eDummy) ts)] undef
      conEqnGet (Constr _ _ c (Right fts)) = eEqn [conApp] $ if fld `elem` fs then rhs else undef
        where fs = map fst fts
              conApp = eApps (EVar c) (map EVar fs)
              rhs = eFld
      conEqnSet (Constr _ _ c (Left ts))   = eEqn [eDummy, eApps (EVar c) (map (const eDummy) ts)] undef
      conEqnSet (Constr _ _ c (Right fts)) = eEqn [eDummy, conApp] $ if fld `elem` fs then rhs else undef
        where fs = map fst fts
              conApp = eApps (EVar c) (map EVar fs)
              rhs = eLam [eFld] conApp
      getName = mkGetName tycon fld

      -- XXX A hack, we can't handle forall yet.
      validType EForall{} = False
      validType _         = True

  pure $ [ Sign [getName] $ eForall iks $ lhsToType (qtycon, iks) `tArrow` fldty
         , Fcn getName $ map conEqnGet cs ]
    ++ if not (validType fldty) then [] else
         [ Instance hdrGet [Fcn igetField [eEqn [eDummy] $ EVar getName] ]
         , Instance hdrSet [Fcn isetField $ map conEqnSet cs]
         ]

mkGetName :: Ident -> Ident -> Ident
mkGetName tycon fld = qualIdent (mkIdent "get") $ qualIdent tycon fld

--------------------------------------------

derTypeable :: Deriver
derTypeable _ 0 (i, _) _ etyp = do
  mn <- gets moduleName
  let
    loc = getSLoc i
    itypeRep  = mkIdentSLoc loc "typeRep"
    imkTyConApp = mkBuiltin loc "mkTyConApp"
    imkTyCon = mkBuiltin loc "mkTyCon"
    hdr = EApp etyp (EVar $ qualIdent mn i)
    mdl = ELit loc $ LStr $ unIdent mn
    nam = ELit loc $ LStr $ unIdent i
    eqns = eEqns [eDummy] $ eAppI2 imkTyConApp (eAppI2 imkTyCon mdl nam) (EListish (LList []))
    inst = Instance hdr [Fcn itypeRep eqns]
  return [inst]
derTypeable _ _ lhs _ e = cannotDerive lhs e

--------------------------------------------

getFieldTys :: Either [SType] [ConstrField] -> [EType]
getFieldTys (Left ts)  = map snd ts
getFieldTys (Right ts) = map (snd . snd) ts

decomp :: EType -> [EType]
decomp t =
  case getAppM t of
    Just (c, ts) | isConIdent c -> concatMap decomp ts
    _                           -> [t]

-- If there is no mctx we use the default strategy to derive the instance context.
-- The default strategy basically extracts all subtypes with variables.
mkHdr :: Maybe EConstraint -> LHS -> [Constr] -> EConstraint -> T EConstraint
mkHdr (Just ctx) _ _ _ = return ctx
mkHdr _ lhs@(_, iks) cs cls = do
  ty <- mkLhsTy lhs
  let ctys :: [EType]  -- All top level types used by the constructors.
      ctys = nubBy eqEType [ tt | Constr evs _ _ flds <- cs, ft <- getFieldTys flds, tt <- decomp ft,
                            not $ null $ freeTyVars [tt] \\ map idKindIdent evs, not (eqEType ty tt) ]
  pure $ eForall iks $ addConstraints (map (tApp cls) ctys) $ tApp cls ty

mkLhsTy :: LHS -> T EType
mkLhsTy (t, iks) = do
  mn <- gets moduleName
  return $ tApps (qualIdent mn t) $ map tVarK iks

mkPat :: Constr -> String -> (EPat, [Expr])
mkPat (Constr _ _ c flds) s =
  let n = either length length flds
      loc = getSLoc c
      vs = map (EVar . mkIdentSLoc loc . (s ++) . show) [1..n]
  in  (tApps c vs, vs)

cannotDerive :: LHS -> EConstraint -> T [EDef]
cannotDerive (c, _) e = tcError (getSLoc e) $ "Cannot derive " ++ showEType (EApp e (EVar c))

--------------------------------------------

derEq :: Deriver
derEq mctx 0 lhs cs@(_:_) eeq = do
  hdr <- mkHdr mctx lhs cs eeq
  let loc = getSLoc eeq
      mkEqn c =
        let (xp, xs) = mkPat c "x"
            (yp, ys) = mkPat c "y"
        in  eEqn [xp, yp] $ if null xs then eTrue else foldr1 eAnd $ zipWith eEq xs ys
      eqns = map mkEqn cs ++ [eEqn [eDummy, eDummy] eFalse]
      iEq = mkIdentSLoc loc "=="
      eEq = EApp . EApp (EVar $ mkBuiltin loc "==")
      eAnd = EApp . EApp (EVar $ mkBuiltin loc "&&")
      eTrue = EVar $ mkBuiltin loc "True"
      eFalse = EVar $ mkBuiltin loc "False"
      inst = Instance hdr [Fcn iEq eqns]
--  traceM $ showEDefs [inst]
  return [inst]
derEq _ _ lhs _ e = cannotDerive lhs e

--------------------------------------------

derOrd :: Deriver
derOrd mctx 0 lhs cs@(_:_) eord = do
  hdr <- mkHdr mctx lhs cs eord
  let loc = getSLoc eord
      mkEqn c =
        let (xp, xs) = mkPat c "x"
            (yp, ys) = mkPat c "y"
        in  [eEqn [xp, yp] $ if null xs then eEQ else foldr1 eComb $ zipWith eCompare xs ys
            ,eEqn [xp, eDummy] eLT
            ,eEqn [eDummy, yp] eGT]
      eqns = concatMap mkEqn cs
      iCompare = mkIdentSLoc loc "compare"
      eCompare = EApp . EApp (EVar $ mkBuiltin loc "compare")
      eComb = EApp . EApp (EVar $ mkBuiltin loc "<>")
      eEQ = EVar $ mkBuiltin loc "EQ"
      eLT = EVar $ mkBuiltin loc "LT"
      eGT = EVar $ mkBuiltin loc "GT"
      inst = Instance hdr [Fcn iCompare eqns]
--  traceM $ showEDefs [inst]
  return [inst]
derOrd _ _ lhs _ e = cannotDerive lhs e

--------------------------------------------

derBounded :: Deriver
derBounded mctx 0 lhs cs@(c0:_) ebnd = do
  hdr <- mkHdr mctx lhs cs ebnd
  let loc = getSLoc ebnd
      mkEqn bnd (Constr _ _ c flds) =
        let n = either length length flds
        in  eEqn [] $ tApps c (replicate n (EVar bnd))

      iMinBound = mkIdentSLoc loc "minBound"
      iMaxBound = mkIdentSLoc loc "maxBound"
      minEqn = mkEqn iMinBound c0
      maxEqn = mkEqn iMaxBound (last cs)
      inst = Instance hdr [Fcn iMinBound [minEqn], Fcn iMaxBound [maxEqn]]
  -- traceM $ showEDefs [inst]
  return [inst]
derBounded _ _ lhs _ e = cannotDerive lhs e

--------------------------------------------

derEnum :: Deriver
derEnum mctx 0 lhs cs@(c0:_) enm | all isNullary cs = do
  hdr <- mkHdr mctx lhs cs enm
  let loc = getSLoc enm

      mkFrom (Constr _ _ c _) i =
        eEqn [EVar c] $ ELit loc (LInt i)
      mkTo (Constr _ _ c _) i =
        eEqn [ELit loc (LInt i)] $ EVar c
      eFirstCon = case c0 of Constr _ _ c _ -> tCon c
      eLastCon = case last cs of Constr _ _ c _ -> tCon c

      iFromEnum = mkIdentSLoc loc "fromEnum"
      iToEnum = mkIdentSLoc loc "toEnum"
      iEnumFrom = mkIdentSLoc loc "enumFrom"
      iEnumFromThen = mkIdentSLoc loc "enumFromThen"
      iEnumFromTo = mkBuiltin loc "enumFromTo"
      iEnumFromThenTo = mkBuiltin loc "enumFromThenTo"
      fromEqns = zipWith mkFrom cs [0..]
      toEqns   = zipWith mkTo   cs [0..] ++ [eEqn [eDummy] $ EApp (EVar $ mkBuiltin loc "error") (ELit loc (LStr "toEnum: out of range"))]
      enumFromEqn =
        -- enumFrom x = enumFromTo x (last cs)
        let x = EVar (mkIdentSLoc loc "x")
        in eEqn [x] (eAppI2 iEnumFromTo x eLastCon)
      enumFromThenEqn =
        -- enumFromThen x1 x2 = if fromEnum x2 >= fromEnum x1 then enumFromThenTo x1 x2 (last cs) else enumFromThenTo x1 x2 (head cs)
        let
          x1 = EVar (mkIdentSLoc loc "x1")
          x2 = EVar (mkIdentSLoc loc "x2")
        in eEqn [x1, x2] (EIf (eAppI2 (mkBuiltin loc ">=") (EApp (EVar iFromEnum) x2) (EApp (EVar iFromEnum) x1)) (eAppI3 iEnumFromThenTo x1 x2 eLastCon) (eAppI3 iEnumFromThenTo x1 x2 eFirstCon))
      inst = Instance hdr [Fcn iFromEnum fromEqns, Fcn iToEnum toEqns, Fcn iEnumFrom [enumFromEqn], Fcn iEnumFromThen [enumFromThenEqn]]
  return [inst]
derEnum _ _ lhs _ e = cannotDerive lhs e

isNullary :: Constr -> Bool
isNullary (Constr _ _ _ flds) = either null null flds

--------------------------------------------

derShow :: Deriver
derShow mctx 0 lhs cs@(_:_) eshow = do
  hdr <- mkHdr mctx lhs cs eshow
  let loc = getSLoc eshow
      mkEqn c@(Constr _ _ nm flds) =
        let (xp, xs) = mkPat c "x"
        in  eEqn [varp, xp] $ showRHS nm xs flds

      var = EVar . mkBuiltin loc
      varp = EVar $ mkIdent "p"
      lit = ELit loc

      iShowsPrec = mkIdentSLoc loc "showsPrec"
      eShowsPrec n = eApp2 (var "showsPrec") (lit (LInt n))
      eShowString s = EApp (var "showString") (lit (LStr s))
      eParen n = eApp2 (var "showParen") (eApp2 (var ">") varp (lit (LInt n)))
      eShowL s = foldr1 ejoin . intersperse (eShowString s)
      ejoin = eApp2 (var ".")

      showRHS nm [] _          = eShowString (unIdentPar nm)
      showRHS nm xs (Left   _) = showRHSN nm xs
      showRHS nm xs (Right fs) = showRHSR nm $ zip (map fst fs) xs

      showRHSN nm xs = eParen 10 $ eShowL " " $ eShowString (unIdentPar nm) : map (eShowsPrec 11) xs

      showRHSR nm fxs =
        eShowString (unIdentPar nm ++ "{") `ejoin`
        eShowL "," (map fld fxs) `ejoin`
        eShowString "}"
          where fld (f, x) = eShowString (unIdentPar f ++ "=") `ejoin` eShowsPrec 0 x

      eqns = map mkEqn cs
      inst = Instance hdr [Fcn iShowsPrec eqns]
--  traceM $ showEDefs [inst]
  return [inst]
derShow _ _ lhs _ e = cannotDerive lhs e

unIdentPar :: Ident -> String
unIdentPar i =
  let s = unIdent i
  in  if isAlpha (head s) then s else "(" ++ s ++ ")"

--------------------------------------------

-- Deriving for the fake Data class.
derData :: Deriver
derData mctx _ lhs cs edata = do
  notYet edata
  hdr <- mkHdr mctx lhs cs edata
  let
    inst = Instance hdr []
  return [inst]

--------------------------------------------

derRead :: Deriver
derRead mctx 0 lhs cs eread = do
  notYet eread
  hdr <- mkHdr mctx lhs cs eread
  let
    loc = getSLoc eread
    iReadPrec = mkIdentSLoc loc "readPrec"
    err = eEqn [] $ EApp (EVar $ mkBuiltin loc "error") (ELit loc (LStr "readPrec not defined"))
    inst = Instance hdr [Fcn iReadPrec [err]]
  return [inst]
derRead _ _ lhs _ e = cannotDerive lhs e

--------------------------------------------

newtypeDer :: Maybe EConstraint -> Int -> LHS -> Constr -> EConstraint -> Maybe EConstraint -> T [EDef]
newtypeDer mctx narg (tycon, iks) c acls mvia = do
  let loc = getSLoc cls
      (clsIks, cls) = unForall acls
      oldty' =                           -- the underlying type, full
        case c of
          Constr [] [] _ (Left [(False, t)])   -> t
          Constr [] [] _ (Right [(_, (_, t))]) -> t
          _                                    -> error "newtypeDer"
--  traceM ("newtypeDer " ++ show (mctx, narg, tycon, iks, c, acls, mvia, oldty'))
  viaty <-
    case mvia of
      Just via -> return via
      Nothing  ->
        case etaReduce (takeEnd narg iks) oldty' of  -- the underlying type, eta reduced
          ([], rt) -> return rt
          _        -> tcError loc "Bad deriving"
  hdr <-
    case mctx of
      Nothing -> do
        let iks' = dropEnd narg iks
        newty <- mkLhsTy (tycon, iks')         -- the newtype, eta reduced
        -- XXX repeats what we might have done above
        oldty <- case etaReduce (takeEnd narg iks) oldty' of  -- the underlying type, eta reduced
                   ([], rt) -> return rt
                   _        -> tcError loc "Bad deriving"
        let ctxOld = tApp cls viaty
            coOldNew = mkCoercible loc oldty newty
            coOldVia =
              case mvia of  -- the via type is also eta reduced
                Just via -> [mkCoercible loc via newty]
                Nothing  -> []
            ctx = filter (not . null . freeTyVars . (:[])) (ctxOld : coOldNew : coOldVia)
        pure (eForall (clsIks ++ iks') $ addConstraints ctx $ tApp cls newty)
      Just hdr -> pure hdr
--  traceM ("newtypeDer: " ++ show (hdr, newty, viaty))
  ----
  let qiCls = getAppCon cls
      clsQual = qualOf qiCls
  ct <- gets classTable
  (ClassInfo _ _ _ mits _) <-
    case M.lookup qiCls ct of
      Nothing -> tcError loc $ "not a class " ++ showIdent qiCls
      Just x  -> return x

  -- hdr looks like forall vs . ctx => C t1 ... tn
  let (_, newtys) = getApp $ dropContext $ dropForall hdr
      mkMethod (mi, amty) = do
        let (tvs, mty) =
              case amty of
                EForall _ xs (EApp (EApp _implies _Ca) t) -> (map idKindIdent xs, t)
                _                                         -> impossibleShow amty
            qvar t = EQVar t kType
            nty =
              if length tvs /= length newtys then error "mkMethod: arity" else
              case subst (zip tvs newtys) mty of
                EForall q vks t -> EForall q (map (\ (IdKind i _) -> IdKind i (EVar dummyIdent)) vks) $ qvar t
                t -> qvar t

            vty = qvar $ dropContext $ dropForall $ subst (zip tvs (init newtys ++ [viaty])) mty
            msign = Sign [mi] nty
            qmi = EQVar (EVar $ qualIdent clsQual mi) amty   -- Use a qualified name for the method
            body = Fcn mi [eEqn [] $ eAppI2 (mkBuiltin loc "coerce") (ETypeArg vty) qmi]
        return [msign, body]
  body <- concat <$> mapM mkMethod mits

--  traceM $ "newtypeDer: " ++ show (Instance hdr body)
  return [Instance hdr body]

dropForall :: EType -> EType
dropForall (EForall _ _ t) = dropForall t
dropForall t               = t

dropContext :: EType -> EType
dropContext t =
  case getImplies t of
    Just (_, t') -> dropContext t'
    _            -> t

{-
freshForall :: EType -> EType
freshForall (EForall _ iks t) = EForall True (map (\ (IdKind i _) -> IdKind i (EVar dummyIdent)) iks) $ freshForall t
freshForall t = t
-}

-- Eta reduce as many of the variables as possible.
-- E.g. etaReduce [a,b] (T a b) = ([], T)
--      etaReduce [a,b] (T Int b) = ([a], T Int)
etaReduce :: [IdKind] -> EType -> ([IdKind], EType)
etaReduce ais = eta (reverse ais)
  where eta (IdKind i _ : is) (EApp t (EVar i')) | i == i' && i `notElem` freeTyVars [t] = eta is t
        eta is t = (reverse is, t)

anyclassDer :: Maybe EConstraint -> Int -> LHS -> EConstraint -> T [EDef]
anyclassDer mctx _ lhs cls = do
  hdr <- mkHdr mctx lhs [] cls
  return [Instance hdr []]
