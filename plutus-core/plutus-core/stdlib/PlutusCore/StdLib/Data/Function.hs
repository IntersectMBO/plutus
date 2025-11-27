-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- | Combinators.
module PlutusCore.StdLib.Data.Function
  ( const
  , idFun
  , applyFun
  , selfData
  , unroll
  , fix
  , fixAndType
  , fixBy
  , fixByAndType
  , fixN
  , fixNAndType
  , FunctionDef (..)
  , getMutualFixOf
  , getSingleFixOf
  ) where

import PlutusPrelude
import Prelude hiding (const)

import PlutusCore.Core
import PlutusCore.MkPlc
import PlutusCore.Name.Unique
import PlutusCore.Quote

import PlutusCore.StdLib.Meta.Data.Tuple
import PlutusCore.StdLib.Type

import Control.Lens.Indexed (ifor)
import Control.Monad

{-| 'id' as a PLC term.

> /\(A :: *) -> \(x : A) -> x -}
idFun :: TermLike term TyName Name uni fun => term ()
idFun = runQuote $ do
  a <- freshTyName "a"
  x <- freshName "x"
  return
    . tyAbs () a (Type ())
    . lamAbs () x (TyVar () a)
    $ var () x

{-| 'const' as a PLC term.

> /\(A B :: *) -> \(x : A) (y : B) -> x -}
const :: TermLike term TyName Name uni fun => term ()
const = runQuote $ do
  a <- freshTyName "a"
  b <- freshTyName "b"
  x <- freshName "x"
  y <- freshName "y"
  return
    . tyAbs () a (Type ())
    . tyAbs () b (Type ())
    . lamAbs () x (TyVar () a)
    . lamAbs () y (TyVar () b)
    $ var () x

{-| '($)' as a PLC term.

> /\(A B :: *) -> \(f : A -> B) (x : A) -> f x -}
applyFun :: TermLike term TyName Name uni fun => term ()
applyFun = runQuote $ do
  a <- freshTyName "a"
  b <- freshTyName "b"
  f <- freshName "f"
  x <- freshName "x"
  return
    . tyAbs () a (Type ())
    . tyAbs () b (Type ())
    . lamAbs () f (TyFun () (TyVar () a) $ TyVar () b)
    . lamAbs () x (TyVar () a)
    $ apply () (var () f) (var () x)

{- Note [Recursion combinators]
We create singly recursive and mutually recursive functions using different combinators.

For singly recursive functions we use the Z combinator (a strict cousin of the Y combinator) that in
UPLC looks like this:

    \f -> (\s -> s s) (\s -> f (\x -> s s x))

We have benchmarked its Haskell version at
  https://github.com/IntersectMBO/plutus/tree/9538fc9829426b2ecb0628d352e2d7af96ec8204/doc/notes/fomega/z-combinator-benchmarks
and observed that in Haskell there's no detectable difference in performance of functions defined
using explicit recursion versus the Z combinator. However Haskell is a compiled language and Plutus
is interpreted, so it's very likely that natively supporting recursion in Plutus instead of
compiling recursive functions to combinators would significantly boost performance.

We've tried using

   \f -> (\s -> s s) (\s x -> f (s s) x)

instead of

   \f -> (\s -> s s) (\s -> f (\x -> s s x))

and while it worked OK at the PLC level, it wasn't a suitable primitive for compilation of recursive
functions, because it would add laziness in unexpected places, see
  https://github.com/IntersectMBO/plutus/issues/5961
so we had to change it.

We use

   \f -> (\s -> s s) (\s x -> f (s s) x)

instead of the more standard

   \f -> (\s x -> f (s s) x) (\s x -> f (s s) x)

because in practice @f@ gets inlined and we wouldn't be able to do so if it occurred twice in the
term. Plus the former also allows us to save on the size of the term.

For mutually recursive functions we use the 'fixBy' combinator, which is, to the best of our
knowledge, our own invention. It was first described at
  https://github.com/IntersectMBO/plutus/blob/067e74f0606fddc5e183dd45209b461e293a6224/doc/notes/fomega/mutual-term-level-recursion/FixN.agda
and fully specified in our "Unraveling recursion: compiling an IR with recursion to System F" paper.
-}

{-| @Self@ as a PLC type.

> fix \(self :: * -> *) (a :: *) -> self a -> a -}
selfData :: RecursiveType uni fun ()
selfData = runQuote $ do
  self <- freshTyName "self"
  a <- freshTyName "a"
  makeRecursiveType () self [TyVarDecl () a $ Type ()]
    . TyFun () (TyApp () (TyVar () self) (TyVar () a))
    $ TyVar () a

{-| @unroll@ as a PLC term.

> /\(a :: *) -> \(s : self a) -> unwrap s s -}
unroll :: TermLike term TyName Name uni fun => term ()
unroll = runQuote $ do
  let self = _recursiveType selfData
  a <- freshTyName "a"
  s <- freshName "s"
  return
    . tyAbs () a (Type ())
    . lamAbs () s (TyApp () self $ TyVar () a)
    . apply () (unwrap () $ var () s)
    $ var () s

{-| 'fix' as a PLC term.

> /\(a b :: *) -> \(f : (a -> b) -> a -> b) ->
>     unroll {a -> b} (iwrap selfF (a -> b) \(s : self (a -> b)) ->
>         f (\(x : a) -> unroll {a -> b} s x))

See @plutus/runQuote $ docs/fomega/z-combinator-benchmarks@ for details. -}
fix :: TermLike term TyName Name uni fun => term ()
fix = fst fixAndType

fixAndType :: TermLike term TyName Name uni fun => (term (), Type TyName uni ())
fixAndType = runQuote $ do
  let RecursiveType self wrapSelf = selfData
  a <- freshTyName "a"
  b <- freshTyName "b"
  f <- freshName "f"
  s <- freshName "s"
  x <- freshName "x"
  let funAB = TyFun () (TyVar () a) $ TyVar () b
      unrollFunAB = tyInst () unroll funAB
  let selfFunAB = TyApp () self funAB
  let fixTerm =
        tyAbs () a (Type ())
          . tyAbs () b (Type ())
          . lamAbs () f (TyFun () funAB funAB)
          . apply () unrollFunAB
          . wrapSelf [funAB]
          . lamAbs () s selfFunAB
          . apply () (var () f)
          . lamAbs () x (TyVar () a)
          $ mkIterAppNoAnn
            unrollFunAB
            [ var () s
            , var () x
            ]
  let fixType =
        TyForall () a (Type ())
          . TyForall () b (Type ())
          $ TyFun () (TyFun () funAB funAB) funAB
  pure (fixTerm, fixType)

{-| A type that looks like a transformation.

> trans F G Q : F Q -> G Q -}
trans :: Type tyname uni () -> Type tyname uni () -> Type tyname uni () -> Quote (Type tyname uni ())
trans f g q = pure $ TyFun () (TyApp () f q) (TyApp () g q)

{-| A type that looks like a natural transformation, sometimes written 'F ~> G'.

> natTrans F G : forall Q :: * . F Q -> G Q -}
natTrans :: Type TyName uni () -> Type TyName uni () -> Quote (Type TyName uni ())
natTrans f g = freshTyName "Q" >>= \q -> TyForall () q (Type ()) <$> trans f g (TyVar () q)

{-| A type that looks like a natural transformation to Id.

> natTransId F : forall Q :: * . F Q -> Q -}
natTransId :: Type TyName uni () -> Quote (Type TyName uni ())
natTransId f = do
  q <- freshTyName "Q"
  pure $ TyForall () q (Type ()) (TyFun () (TyApp () f (TyVar () q)) (TyVar () q))

{-| The 'fixBy' combinator.

> fixBy :
>     forall (F :: * -> *) .
>     ((F ~> Id) -> (F ~> Id)) ->
>     ((F ~> F) -> (F ~> Id)) -}
fixBy :: TermLike term TyName Name uni fun => term ()
fixBy = fst fixByAndType

fixByAndType :: TermLike term TyName Name uni fun => (term (), Type TyName uni ())
fixByAndType = runQuote $ do
  f <- freshTyName "F"

  -- by : (F ~> Id) -> (F ~> Id)
  by <- freshName "by"
  byTy <- do
    nt1 <- natTransId (TyVar () f)
    nt2 <- natTransId (TyVar () f)
    pure $ TyFun () nt1 nt2

  resTy <- do
    nt1 <- natTrans (TyVar () f) (TyVar () f)
    nt2 <- natTransId (TyVar () f)
    pure $ TyFun () nt1 nt2

  -- instantiatedFix = fix {F ~> F} {F ~> Id}
  instantiatedFix <- do
    nt1 <- natTrans (TyVar () f) (TyVar () f)
    nt2 <- natTransId (TyVar () f)
    pure $ tyInst () (tyInst () fix nt1) nt2

  -- rec : (F ~> F) -> (F ~> Id)
  recc <- freshName "rec"
  reccTy <- do
    nt <- natTrans (TyVar () f) (TyVar () f)
    nt2 <- natTransId (TyVar () f)
    pure $ TyFun () nt nt2

  -- h : F ~> F
  h <- freshName "h"
  hty <- natTrans (TyVar () f) (TyVar () f)

  -- R :: *
  -- fr : F R
  r <- freshTyName "R"
  fr <- freshName "fr"
  let frTy = TyApp () (TyVar () f) (TyVar () r)

  -- Q :: *
  -- fq : F Q
  q <- freshTyName "Q"
  fq <- freshName "fq"
  let fqTy = TyApp () (TyVar () f) (TyVar () q)

  -- inner = (/\ (Q :: *) -> \ q : F Q -> rec h {Q} (h {Q} q))
  let inner =
        apply () (var () by) $
          tyAbs () q (Type ()) $
            lamAbs () fq fqTy $
              apply () (tyInst () (apply () (var () recc) (var () h)) (TyVar () q)) $
                apply () (tyInst () (var () h) (TyVar () q)) (var () fq)
  let fixByTerm =
        tyAbs () f (KindArrow () (Type ()) (Type ())) $
          lamAbs () by byTy $
            apply () instantiatedFix $
              lamAbs () recc reccTy $
                lamAbs () h hty $
                  tyAbs () r (Type ()) $
                    lamAbs () fr frTy $
                      apply () (tyInst () inner (TyVar () r)) (var () fr)
  let fixByType =
        TyForall () f (KindArrow () (Type ()) (Type ())) $
          TyFun () byTy resTy
  pure (fixByTerm, fixByType)

{-| Make a @n@-ary fixpoint combinator.

> FixN n :
>     forall A1 B1 ... An Bn :: * .
>     (forall Q :: * .
>         ((A1 -> B1) -> ... -> (An -> Bn) -> Q) ->
>         (A1 -> B1) ->
>         ... ->
>         (An -> Bn) ->
>         Q) ->
>     (forall R :: * . ((A1 -> B1) -> ... (An -> Bn) -> R) -> R) -}
fixN :: TermLike term TyName Name uni fun => Integer -> term () -> term ()
fixN n fixByTerm = fst (fixNAndType n fixByTerm)

fixNAndType :: TermLike term TyName Name uni fun => Integer -> term () -> (term (), Type TyName uni ())
fixNAndType n fixByTerm = runQuote $ do
  -- the list of pairs of A and B types
  asbs <- replicateM (fromIntegral n) $ do
    a <- freshTyName "a"
    b <- freshTyName "b"
    pure (a, b)

  let abFuns = fmap (\(a, b) -> TyFun () (TyVar () a) (TyVar () b)) asbs
  let abTyVars = concatMap (\(a, b) -> [TyVarDecl () a (Type ()), TyVarDecl () b (Type ())]) asbs

  -- funTysTo X = (A1 -> B1) -> ... -> (An -> Bn) -> X
  let funTysTo = mkIterTyFun () abFuns

  -- the type of fixN, as in the header comment
  fixNType <- do
    q <- freshTyName "Q"
    let qvar = TyVar () q
    let argTy = TyForall () q (Type ()) (TyFun () (funTysTo qvar) (funTysTo qvar))
    r <- freshTyName "R"
    let rvar = TyVar () r
    let resTy = TyForall () r (Type ()) (TyFun () (funTysTo rvar) rvar)
    let fullTy = mkIterTyForall abTyVars $ TyFun () argTy resTy
    pure fullTy

  -- instantiatedFix = fixBy { \X :: * -> (A1 -> B1) -> ... -> (An -> Bn) -> X }
  instantiatedFix <- do
    x <- freshTyName "X"
    pure $ tyInst () fixByTerm (TyLam () x (Type ()) (funTysTo (TyVar () x)))

  -- f : forall Q :: * . ((A1 -> B1) -> ... -> (An -> Bn) -> Q) -> (A1 -> B1) -> ... -> (An -> Bn) -> Q)
  f <- freshName "f"
  fTy <- do
    q <- freshTyName "Q"
    pure $ TyForall () q (Type ()) $ TyFun () (funTysTo (TyVar () q)) (funTysTo (TyVar () q))

  -- k : forall Q :: * . ((A1 -> B1) -> ... -> (An -> Bn) -> Q) -> Q)
  k <- freshName "k"
  kTy <- do
    q <- freshTyName "Q"
    pure $ TyForall () q (Type ()) $ TyFun () (funTysTo (TyVar () q)) (TyVar () q)

  s <- freshTyName "S"

  -- h : (A1 -> B1) -> ... -> (An -> Bn) -> S
  h <- freshName "h"
  let hTy = funTysTo (TyVar () s)

  -- branch (ai, bi) i = \x : ai -> k { bi } \(f1 : A1 -> B1) ... (fn : An -> Bn) . fi x
  let branch (a, b) i = do
        -- names and types for the f arguments
        fs <- ifor asbs $ \j (a', b') -> do
          f_j <- freshName $ "f_" <> showText j
          pure $ VarDecl () f_j (TyFun () (TyVar () a') (TyVar () b'))

        x <- freshName "x"

        pure $
          lamAbs () x (TyVar () a) $
            apply () (tyInst () (var () k) (TyVar () b)) $
              mkIterLamAbs fs $
                -- this is an ugly but straightforward way of getting the right fi
                apply () (mkVar (fs !! i)) (var () x)

  -- a list of all the branches
  branches <- forM (zip asbs [0 ..]) $ uncurry branch

  -- [A1, B1, ..., An, Bn]
  let allAsBs = foldMap (\(a, b) -> [a, b]) asbs
  let fixNTerm =
        -- abstract out all the As and Bs
        mkIterTyAbs (fmap (\tn -> TyVarDecl () tn (Type ())) allAsBs) $
          lamAbs () f fTy $
            mkIterAppNoAnn
              instantiatedFix
              [ lamAbs () k kTy $
                  tyAbs () s (Type ()) $
                    lamAbs () h hTy $
                      mkIterAppNoAnn (var () h) branches
              , var () f
              ]
  pure (fixNTerm, fixNType)

-- See Note [Recursion combinators].
-- | Get the fixed-point of a single recursive function.
getSingleFixOf
  :: TermLike term TyName Name uni fun
  => ann -> term ann -> FunctionDef term TyName Name uni fun ann -> term ann
getSingleFixOf ann fix1 fun@FunctionDef {_functionDefType = (FunctionType _ dom cod)} =
  let instantiatedFix = mkIterInst fix1 [(ann, dom), (ann, cod)]
      abstractedBody = mkIterLamAbs [functionDefVarDecl fun] $ _functionDefTerm fun
   in apply ann instantiatedFix abstractedBody

-- See Note [Recursion combinators].
{-| Get the fixed-point of a list of mutually recursive functions.

> MutualFixOf _ fixN [ FunctionDef _ fN1 (FunctionType _ a1 b1) f1
>                    , ...
>                    , FunctionDef _ fNn (FunctionType _ an bn) fn
>                    ] =
>     Tuple [(a1 -> b1) ... (an -> bn)] $
>         fixN {a1} {b1} ... {an} {bn}
>             /\(q :: *) -> \(choose : (a1 -> b1) -> ... -> (an -> bn) -> q) ->
>                 \(fN1 : a1 -> b1) ... (fNn : an -> bn) -> choose f1 ... fn -}
getMutualFixOf
  :: TermLike term TyName Name uni fun
  => ann -> term ann -> [FunctionDef term TyName Name uni fun ann] -> Quote (Tuple term uni ann)
getMutualFixOf ann fixn funs = do
  let funTys = map functionDefToType funs

  q <- liftQuote $ freshTyName "Q"
  -- TODO: It was 'safeFreshName' previously. Should we perhaps have @freshName = safeFreshName@?
  choose <- freshName "choose"
  let chooseTy = mkIterTyFun ann funTys (TyVar ann q)

  -- \v1 ... vn -> choose f1 ... fn
  let rhss = map _functionDefTerm funs
      chosen = mkIterApp (var ann choose) ((ann,) <$> rhss)
      vsLam = mkIterLamAbs (map functionDefVarDecl funs) chosen

  -- abstract out Q and choose
  let cLam = tyAbs ann q (Type ann) $ lamAbs ann choose chooseTy vsLam

  -- fixN {A1} {B1} ... {An} {Bn}
  instantiatedFix <- do
    let domCods = foldMap (\(FunctionDef _ _ (FunctionType _ dom cod) _) -> [dom, cod]) funs
    pure $ mkIterInst fixn ((ann,) <$> domCods)

  let term = apply ann instantiatedFix cLam

  pure $ Tuple funTys term
