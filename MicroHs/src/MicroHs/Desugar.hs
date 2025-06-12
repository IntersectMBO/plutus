-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns -Wno-unused-imports -Wno-dodgy-imports #-}
module MicroHs.Desugar(
  desugar,
  LDef, showLDefs,
  encodeInteger,
  ) where
import qualified Prelude(); import MHSPrelude
import Data.Char
import Data.Function
import Data.Integer(_integerToIntList)
import Data.List
import Data.Maybe
import Data.Ratio
import Debug.Trace
import GHC.Stack

import MicroHs.EncodeData
import MicroHs.Expr
import MicroHs.Exp
import MicroHs.Flags
import MicroHs.Graph
import MicroHs.Ident
import MicroHs.List
import MicroHs.State as S
import MicroHs.TypeCheck

type LDef = (Ident, Exp)

desugar :: Flags -> TModule [EDef] -> TModule [LDef]
desugar flags tm =
  setBindings tm (map lazier $ checkDup $ concatMap (dsDef flags (tModuleName tm)) (tBindingsOf tm))

dsDef :: Flags -> IdentModule -> EDef -> [LDef]
dsDef flags mn adef =
  case adef of
    Data _ cs _ ->
      let
        n = length cs
        dsConstr i (Constr _ ctx c ets) =
          let
            ss = (if null ctx then [] else [False]) ++
                 map fst (either id (map snd) ets)   -- strict flags
          in (qualIdent mn c, encConstr i n ss)
      in  zipWith dsConstr [0::Int ..] cs
    Newtype _ (Constr _ _ c _) _ -> [ (qualIdent mn c, Lit (LPrim "I")) ]
    Fcn f eqns -> [(f, wrapTick (useTicks flags) f $ dsEqns (getSLoc f) eqns)]
    PatBind p e ->
      case patVarsQ p of
        [] -> []    -- no bound variable, just throw it away
        -- Create a unique varible by adding a "$g" suffix to one of the bound variables.
        v : _ -> dsPatBind (addIdentSuffix v "$g") p e
    ForImp ie i t -> [(i, if isIO t then frgn else App perf frgn)]
      where frgn = Lit $ LForImp (fromMaybe (unIdent (unQualIdent i)) ie) cty
            cty = CType t
            perf = Lit $ LPrim "IO.performIO"
            isIO x | Just (_, r) <- getArrow x = isIO r
            isIO (EApp (EVar io) _) = io == mkIdent "Primitives.IO"
            isIO _ = False
    Class ctx (c, _) _ bs ->
      let f = mkIdent "$f"
          meths :: [Ident]
          meths = [ qualIdent mn i | (Sign is _) <- bs, i <- is ]
          supers :: [Ident]
          supers = [ qualIdent mn $ mkSuperSel c i | i <- [1 .. length ctx] ]
          xs = [ mkIdent ("$x" ++ show j) | j <- [ 1 .. length ctx + length meths ] ]
      in  (qualIdent mn $ mkClassConstructor c, lams xs $ Lam f $ apps (Var f) (map Var xs)) :
          zipWith (\ i x -> (i, Lam f $ App (Var f) (lams xs $ Var x))) (supers ++ meths) xs
    _ -> []

wrapTick :: Bool -> Ident -> Exp -> Exp
wrapTick False _ ee = ee
wrapTick True  i ee = wrap ee
  where tick = Lit (LTick (unIdent i))
        wrap (Lam x e) = Lam x (wrap e)
        wrap e = App tick e
{- This kills the automagic specialization.
wrapTick True  i ee = wrap 0 ee
  where wrap n e = App (Lit (LTick (unIdent i ++ "-" ++ show (n::Int)))) e'
          where e' = case e of
                       Lam x a -> Lam x (wrap (n+1) a)
                       _ -> e
-}

oneAlt :: Expr -> EAlts
oneAlt e = EAlts [([], e)] []

dsBind :: Ident -> EBind -> [LDef]
dsBind v abind =
  case abind of
    Fcn f eqns -> [(f, dsEqns (getSLoc f) eqns)]
    PatBind p e -> dsPatBind v p e
    _ -> []

dsPatBind :: Ident -> EPat -> Expr -> [LDef]
dsPatBind v p e =
  let de = (v, dsExpr e)
      ds = [ (i, dsExpr (ECase (EVar v) [(p, oneAlt $ EVar i)])) | i <- patVarsQ p ]
  in  de : ds

-- patVars does not work wth qualified bound variable names,
-- but that's what we get for a top level PatBind
patVarsQ :: EPat -> [Ident]
patVarsQ = filter (\ i -> not (isDummyIdent i) && not (isConIdent $ unQualIdent i)) . allVarsExpr

dsEqns :: SLoc -> [Eqn] -> Exp
dsEqns loc eqns =
  case eqns of
    Eqn aps _ : _ ->
      let
        vs = allVarsBind $ Fcn (mkIdent "") eqns
        xs = take (length aps) $ newVars "$q" vs
        mkArm (Eqn ps alts) =
          let ps' = map dsPat ps
          in  (ps', dsAlts alts)
        ex = dsCaseExp loc (vs ++ xs) (map Var xs) (map mkArm eqns)
      in foldr Lam ex xs
    _ -> eMatchErr loc

dsAlts :: EAlts -> (Exp -> Exp)
dsAlts (EAlts alts bs) = dsBinds bs . dsAltsL alts

dsAltsL :: [EAlt] -> (Exp -> Exp)
dsAltsL []                 dflt = dflt
dsAltsL [([], e)]             _ = dsExpr e  -- fast special case
dsAltsL ((ss, rhs) : alts) dflt =
  let
    erest = dsAltsL alts dflt
    x = newVar (allVarsExp erest)
  in eLet x erest (dsExpr $ dsAlt (EVar x) ss rhs)

dsAlt :: Expr -> [EStmt] -> Expr -> Expr
dsAlt _ [] rhs = rhs
dsAlt dflt (SBind p e : ss) rhs = ECase e [(p, EAlts [(ss, rhs)] []), (EVar dummyIdent, oneAlt dflt)]
dsAlt dflt (SThen (EVar i) : ss) rhs | isIdent "Data.Bool.otherwise" i = dsAlt dflt ss rhs
dsAlt dflt (SThen e   : ss) rhs = EIf e (dsAlt dflt ss rhs) dflt
dsAlt dflt (SLet bs   : ss) rhs = ELet bs (dsAlt dflt ss rhs)

dsBinds :: [EBind] -> Exp -> Exp
dsBinds [] ret = ret
dsBinds ads@(PatBind (ELazy False p) e : ds) ret =
  -- Turn a strict let/where into a case.
  -- XXX This does no reordering of bindings.
  let rest = dsBinds ds ret
      used = allVarsExp ret ++ allVarsExpr (ELet ads (ETuple []))
  in  dsCaseExp (getSLoc p) used [dsExpr e] [([dsPat p], const rest)]
dsBinds ads ret =
  let
    avs = concatMap allVarsBind ads
    pvs = newVars "$p" avs
    mvs = newVars "$m" avs
    ds = concat $ zipWith dsBind pvs ads
    node ie@(i, e) = (ie, i, freeVars e)
    gr = map node $ checkDup ds
    asccs = stronglyConnComp gr
    loop _ [] = ret
    loop vs (AcyclicSCC (i, e) : sccs) =
      letE i e $ loop vs sccs
    loop vs (CyclicSCC [(i, e)] : sccs) =
      case lazier (i, e) of
        (i', e')
          | i' `elem` freeVars e' -> letRecE i' e' $ loop vs sccs
          | otherwise -> letE i' e' $ loop vs sccs
    loop vvs (CyclicSCC ies : sccs) =
      let (v:vs) = vvs in
      mutualRec v ies (loop vs sccs)
  in loop mvs asccs

letE :: Ident -> Exp -> Exp -> Exp
letE i e b = eLet i e b          -- do some minor optimizations
             --App (Lam i b) e

-- Do a single recursive definition 'let i = e in b'
-- by 'let i = Y (\i.e) in b'
letRecE :: Ident -> Exp -> Exp -> Exp
letRecE i e b = letE i (App (Lit (LPrim "Y")) (Lam i e)) b

-- Do mutual recursion by tupling up all the definitions.
--  let f = ... g ...
--      g = ... f ...
--  in  body
-- turns into
--  letrec v =
--        let f = sel_0_2 v
--            g = sel_1_2 v
--        in  (... g ..., ... f ...)
--  in
--    let f = sel_0_2 v
--        g = sel_1_2 v
--    in  body
mutualRec :: Ident -> [LDef] -> Exp -> Exp
mutualRec v ies body =
  let (is, es) = unzip ies
      n = length is
      ev = Var v
      one m i = letE i (mkTupleSelE m n ev)
      bnds = foldr (.) id $ zipWith one [0..] is
  in  letRecE v (bnds $ mkTupleE es) $
      bnds body

-- In case we are cross compiling for a 32 bit platform we don't want integers that are too big.
-- So we use the 32 bit bounds on the int encoding.
encodeInteger :: Integer -> Exp
encodeInteger i | -0x80000000 <= i && i <= 0x7fffffff  =
--  trace ("*** small integer " ++ show i) $
  App (Var (mkIdent "Data.Integer_Type._intToInteger")) (Lit (LInt (fromInteger i)))
                | otherwise =
--  trace ("*** large integer " ++ show i) $
  App (Var (mkIdent "Data.Integer._intListToInteger")) (encList (map (Lit . LInt) (_integerToIntList i)))

encodeRational :: Rational -> Exp
encodeRational r =
  App (App (Var (mkIdent "Data.Ratio_Type._mkRational")) (encodeInteger (numerator r))) (encodeInteger (denominator r))

dsExpr :: Expr -> Exp
dsExpr aexpr =
  case aexpr of
    EVar i -> Var i
    EApp (EApp (EVar app) (EListish (LCompr e stmts))) l | app == mkIdent "Data.List_Type.++" ->
      dsExpr $ dsCompr e stmts l
    EApp f a -> App (dsExpr f) (dsExpr a)
    ELam l qs -> dsEqns l qs
    ELit l (LExn s) -> Var (mkIdentSLoc l s)
    ELit _ (LChar c) -> Lit (LInt (ord c))
    ELit _ (LInteger i) -> encodeInteger i
    ELit _ (LRat i) -> encodeRational i
    ELit _ l -> Lit l
    ECase e as -> dsCase (getSLoc aexpr) e as
    ELet ads e -> dsBinds ads (dsExpr e)
    ETuple es -> Lam (mkIdent "$f") $ foldl App (Var $ mkIdent "$f") $ map dsExpr es
    EIf e1 e2 e3 -> encIf (dsExpr e1) (dsExpr e2) (dsExpr e3)
    EListish (LList es) -> encList $ map dsExpr es
    EListish (LCompr e stmts) -> dsExpr $ dsCompr e stmts (EListish (LList []))
    ECon c ->
        case getTupleConstr (conIdent c) of
          Just n ->
            let
              xs = [mkIdent ("x" ++ show i) | i <- [1 .. n] ]
              body = mkTupleE $ map Var xs
            in foldr Lam body xs
          Nothing -> Var (conIdent c)
    _ -> impossibleShow aexpr

dsCompr :: Expr -> [EStmt] -> Expr -> Expr
dsCompr e [] l = EApp (EApp consCon e) l
dsCompr e (SThen c : ss) l = EIf c (dsCompr e ss l) l
dsCompr e (SLet ds : ss) l = ELet ds (dsCompr e ss l)
-- Special case for the idiom [ ... | ..., p <- [x], ... ].  This is a little more efficient.
dsCompr e (SBind p (EListish (LList [x])) : ss) l = ECase x [(p, oneAlt $ dsCompr e ss l), (EVar dummyIdent, oneAlt l)]
dsCompr e xss@(SBind p g : ss) l = ELet [hdef] (EApp eh g)
  where
    hdef = Fcn h [eqn1, eqn2, eqn3]
    eqn1 = eEqn [nilCon] l
    eqn2 = eEqn [EApp (EApp consCon p) vs] (dsCompr e ss (EApp eh vs))
    eqn3 = eEqn [EApp (EApp consCon u) vs]               (EApp eh vs)
    u = EVar dummyIdent
    h = head $ newVars "$h" allVs
    eh = EVar h
    vs = EVar $ head $ newVars "$vs" allVs
    allVs = allVarsExpr (EListish (LCompr (ETuple [e,l]) xss))  -- all used identifiers

-- Use tuple encoding to make a tuple
mkTupleE :: [Exp] -> Exp
mkTupleE = Lam (mkIdent "$f") . foldl App (Var (mkIdent "$f"))

-- Select component m from an n-tuple
mkTupleSelE :: Int -> Int -> Exp -> Exp
mkTupleSelE m n tup =
  let
    xs = [mkIdent ("x" ++ show i) | i <- [1 .. n] ]
  in App tup (foldr Lam (Var (xs !! m)) xs)

-- Handle special syntax for lists and tuples.
dsPat :: HasCallStack =>
         EPat -> EPat
dsPat apat =
  case apat of
    EVar _ -> apat
    ECon _ -> apat
    EApp f a -> EApp (dsPat f) (dsPat a)
    EListish (LList ps) -> dsPat $ foldr (EApp . EApp consCon) nilCon ps
    ETuple ps -> dsPat $ foldl EApp (tupleCon (getSLoc apat) (length ps)) ps
    EAt i p -> EAt i (dsPat p)
    ELit loc (LStr cs) | length cs < 2 -> dsPat (EListish (LList (map (ELit loc . LChar) cs)))
    ELit _ _ -> apat
    ENegApp _ -> apat
    EViewPat e p -> EViewPat e (dsPat p)
    ELazy b pat -> ELazy b (dsPat pat)
    _ -> impossible

iNil :: Ident
iNil = mkIdent $ listPrefix ++ "[]"

iCons :: Ident
iCons = mkIdent $ listPrefix ++ ":"

consCon :: EPat
consCon = ECon $ ConData [(iNil, 0), (iCons, 2)] iCons []

nilCon :: EPat
nilCon = ECon $ ConData [(iNil, 0), (iCons, 2)] iNil []

tupleCon :: SLoc -> Int -> EPat
tupleCon loc n =
  let
    c = tupleConstr loc n
  in ECon $ ConData [(c, n)] c []

newVars :: String -> [Ident] -> [Ident]
newVars s is = deleteAllsBy (==) [ mkIdent (s ++ show i) | i <- [1::Int ..] ] is

newVar :: [Ident] -> Ident
newVar = head . newVars "$v"

showLDefs :: [LDef] -> String
showLDefs = unlines . map showLDef

showLDef :: LDef -> String
showLDef a =
  case a of
    (i, e) -> showIdent i ++ " = " ++ show e

----------------

dsCase :: HasCallStack => SLoc -> Expr -> [ECaseArm] -> Exp
dsCase loc ae as =
  dsCaseExp loc usedVars [dsExpr ae] (map mkArm as)
  where
    usedVars = allVarsExpr (ECase ae as)
    mkArm :: ECaseArm -> Arm
    mkArm (p, alts) =
      let p' = dsPat p
      in  ([p'], dsAlts alts)

type MState = [Ident]  -- supply of unused variables.

type M a = State MState a
type Arm = ([EPat], Exp -> Exp)  -- Patterns, and a function that expects the default (which might be ignored).
type Matrix = [Arm]

newIdents :: Int -> M [Ident]
newIdents n = do
  is <- get
  put (drop n is)
  return (take n is)

newIdent :: M Ident
newIdent = do
  is <- get
  put (tail is)
  return (head is)

dsCaseExp :: HasCallStack => SLoc -> [Ident] -> [Exp] -> Matrix -> Exp
dsCaseExp loc used ss mtrx =
  let
    supply = newVars "$x" used
    ds xs aes =
      case aes of
        []   -> dsMatrixL (eMatchErr loc) (reverse xs) mtrx
        e:es -> letBind (return e) $ \ x -> ds (x:xs) es
  in evalState (ds [] ss) supply

-- Handle lazy and strict bindings
dsMatrixL :: HasCallStack =>
             Exp -> [Exp] -> Matrix -> M Exp
dsMatrixL dflt is arms = dsMatrix dflt is (map dsLazy arms)

dsLazy :: Arm -> Arm
dsLazy (ps, rhs) =
  -- Accumulate lazy bindings and strict bindings
  let ((_, rbs, ris), ps') = mapAccumL lazy (1, [], []) ps
      lazy :: (Int, [EBind], [Exp]) -> EPat -> ((Int, [EBind], [Exp]), EPat)
      lazy s@(n, bs, is) ap =
        case ap of
          ELazy False p'@(EVar i) | not (isDummyIdent i)        -- XXX !_ doesn't work
                                  -> ((n, bs, Var i : is), p')
          ELazy False p'          -> lazy (n, bs, is) p'        -- ignore ! on non-variables for now
          ELazy True  p'          -> ((n+1, b:bs, is), EVar v)
            where v = mkIdent ("~" ++ show n)
                  b = PatBind p' (EVar v)
          EVar _                  -> (s, ap)
          EViewPat e p            -> (s', EViewPat e p') where (s', p')  = lazy s p
          ECon _                  -> (s, ap)
          EApp p1 p2              -> (s'', EApp p1' p2') where (s', p1') = lazy s p1; (s'', p2') = lazy s' p2
          EAt i p                 -> (s', EAt i p')      where (s', p')  = lazy s p
          _                       -> impossible
  in  (ps', \ d -> dsBinds (reverse rbs) $ foldr eSeq (rhs d) (reverse ris))

eSeq :: Exp -> Exp -> Exp
eSeq e1 e2 = App (App (Lit (LPrim "seq")) e1) e2

-- XXX quadratic.  but only used for short lists
groupEq :: forall a . (a -> a -> Bool) -> [a] -> [[a]]
groupEq eq axs =
  case axs of
    [] -> []
    x:xs ->
      case partition (eq x) xs of
        (es, ns) -> (x:es) : groupEq eq ns

-- Desugar a pattern matrix.
-- The input is a (usually identifier) vector e1, ..., en
-- and patterns matrix p11, ..., p1n   -> e1
--                     p21, ..., p2n
--                     pm1, ..., pmn   -> em
-- Note that the RHSs are of type Exp.
dsMatrix :: HasCallStack =>
            Exp -> [Exp] -> Matrix -> M Exp
--dsMatrix dflt is aarms | trace (show (dflt, is)) False = undefined
dsMatrix dflt _ [] = return dflt
dsMatrix dflt []         aarms =
  -- We can have several arms if there are guards.
  -- Combine them in order.
  return $ foldr snd dflt aarms
dsMatrix dflt iis@(i:is) aarms@(aarm : aarms') =
  case leftMost aarm of
    EVar _ -> do
      -- Find all variables, substitute with i, and proceed
      let (vars, nvars) = span (isPVar . leftMost) aarms
          vars' = map (sub . unAt i) vars
          sub (EVar x : ps, rhs) = (ps, substAlpha x i . rhs)
          sub _ = impossible
      letBind (dsMatrix dflt iis nvars) $ \ drest ->
        dsMatrix drest is vars'
    -- Collect identical transformations, do the transformation and proceed.
    EViewPat e _ -> do
      let (views, nviews) = span (isPView e . leftMost) aarms'
      letBind (dsMatrix dflt iis nviews) $ \ drest ->
        letBind (return $ App (dsExpr e) i) $ \ vi -> do
        let views' = map (unview . unAt i) (aarm : views)
            unview (EViewPat _ p:ps, rhs) = (p:ps, rhs)
            unview _ = impossible
        dsMatrix drest (vi:is) views'
    -- Collect all constructors, group identical ones.
    _ -> do             -- must be ECon/EApp
      let
        (cons, ncons) = span (isPCon . leftMost) aarms
      letBind (dsMatrix dflt iis ncons) $ \ drest -> do
        let
          idOf (p:_, _) = pConOf p
          idOf _ = impossible
          grps = groupEq (on (==) idOf) $ map (unAt i) cons
          oneGroup grp = do
            let
              con = pConOf $ leftMost $ head grp
            xs <- newIdents (conArity con)
            let
              one (p : ps, e) = (pArgs p ++ ps, e)
              one _ = impossible
            cexp <- dsMatrix drest (map Var xs ++ is) (map one grp)
            return (SPat con xs, cexp)
        narms <- mapM oneGroup grps
        return $ mkCase i narms drest
  where
    leftMost (p:_, _) = skipEAt p  -- pattern in first column
    leftMost _ = impossible
    skipEAt (EAt _ p) = skipEAt p
    skipEAt p = p
    isPCon (EVar _) = False
    isPCon (EViewPat _ _) = False
    isPCon _ = True
    isPVar (EVar _) = True
    isPVar _ = False
    isPView e (EViewPat e' _) = eqExpr e e'
    isPView _ _ = False
    unAt ii (EAt x p : ps, rhs) = unAt i (p:ps, substAlpha x ii . rhs)
    unAt _ arm = arm

mkCase :: Exp -> [(SPat, Exp)] -> Exp -> Exp
mkCase var pes dflt =
  --trace ("mkCase " ++ show pes) $
  case pes of
    [] -> dflt
    [(SPat (ConNew _ _) [x], arhs)] -> eLet x var arhs
    _ -> encCase var pes dflt

eMatchErr :: SLoc -> Exp
eMatchErr loc =
  let exn = mkIdentSLoc loc "Control.Exception.Internal.patternMatchFail"
      msg = LStr $ show loc
  in  App (Var exn) (Lit msg)

-- If the first expression isn't a variable/literal, then use
-- a let binding and pass variable to f.
letBind :: M Exp -> (Exp -> M Exp) -> M Exp
letBind me f = do
  e <- me
  if cheap e then
    f e
   else do
    x <- newIdent
    r <- f (Var x)
    return $ eLet x e r

cheap :: Exp -> Bool
cheap ae =
  case ae of
    Var _ -> True
    Lit _ -> True
    _ -> False

eLet :: Ident -> Exp -> Exp -> Exp
eLet i e b | cheap e = substExp i e b    -- always inline variables and literals
eLet i e b =
  if i == dummyIdent then
    b
  else
    case b of
      Var j | i == j -> e
      _ ->
        case filter (== i) (freeVars b) of
          []  -> b                -- no occurences, no need to bind
          -- The single use substitution is essential for performance.
          [_] -> substExp i e b   -- single occurrence, substitute  XXX could be worse if under lambda
          _   -> App (Lam i b) e  -- just use a beta redex

-- Change from x to y inside e.
substAlpha :: Ident -> Exp -> Exp -> Exp
substAlpha x y e =
  if x == dummyIdent then
    e
  else
    substExp x y e

pConOf :: HasCallStack =>
          EPat -> Con
pConOf apat =
  case apat of
    ECon c -> c
    EAt _ p -> pConOf p
    EApp p _ -> pConOf p
    _ -> impossibleShow apat

pArgs :: EPat -> [EPat]
pArgs apat =
  case apat of
    ECon _ -> []
    EApp f a -> pArgs f ++ [a]
    ELit _ _ -> []
    _ -> impossible

getDups :: (Ord a) => [a] -> [[a]]
getDups = filter ((> 1) . length) . groupSort

checkDup :: [LDef] -> [LDef]
checkDup ds =
  case getDups $ filter (/= dummyIdent) $ map fst ds of
    [] -> ds
    (i1:_i2:_) : _ ->
      errorMessage (getSLoc i1) $ "duplicate definition " ++ showIdent i1
        -- XXX mysteriously the location for i2 is the same as i1
        -- ++ ", also at " ++ showSLoc (getSLoc i2)
    _ -> error "checkDup"

-- Make recursive definitions lazier.
-- The idea is that we have
--  f x y = ... (f x) ...
-- we turn this into
--  f x = letrec f' y = ... f' ... in f'
-- thus avoiding the extra argument passing.
-- This gives a small speedup with overloading.
lazier :: LDef -> LDef
lazier def@(fcn, l@(Lam _ _)) =
  let fcn' = addIdentSuffix fcn "@"
      vfcn' = Var fcn'
      args :: Exp -> (Exp, [Ident])
      args (Lam x b) = -- (x:) <$> args b
        let (e, xs) = args b
        in  (e, x:xs)
      args e = (e, [])
      (body, as) = args l
      -- Find min # of args that are unchanged in a recursive call.
      -- Here 0 == no recursive calls seen (or only 0-matched calls seen).
      -- We ignore recursive calls with 0 matched args.
      minn :: Int -> Int -> Int
      minn 0 b = b
      minn a 0 = a
      minn a b = min a b
      minMatch :: [Ident] -> Exp -> Int
      minMatch _ (Lam _ e) = minMatch [] e
      minMatch vs (App f (Var v)) = minMatch (v:vs) f
      minMatch _ (App f a) = minMatch [] f `minn` minMatch [] a
      minMatch [] (Var _) = 0
      minMatch vs (Var v) | v == fcn = length (takeWhile id (zipWith (==) vs as))
      minMatch _ _ = 0
      arity = minMatch [] body
      (drops, keeps) = splitAt arity as
      -- reverse n-ary apply
      app :: [Ident] -> Exp -> Exp
      app vs e = apps e (map Var vs)
      -- Replace n recursive args with call to vfcn'
      repl :: [Ident] -> Exp -> Exp
      repl vs (Lam i e) = app vs $ Lam i $ repl [] e
      repl vs (App f (Var v)) = repl (v:vs) f
      repl vs (App f a) = app vs $ App (repl [] f) (repl [] a)
      repl [] (Var v) = Var v
      repl vs (Var v)
        | v == fcn && take arity vs == drops = app (drop arity vs) vfcn'
      repl vs e = app vs e
  in  if arity > 0
      then (fcn, lams drops $ letRecE fcn' (lams keeps (repl [] body)) vfcn')
      else def
lazier def = def
