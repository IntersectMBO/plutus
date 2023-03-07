-- editorconfig-checker-disable-file
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ViewPatterns          #-}

{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module PlutusIR.Generators.QuickCheck.ShrinkTerms where

import PlutusIR.Generators.QuickCheck.Common

import PlutusCore.Generators.QuickCheck.Builtin
import PlutusCore.Generators.QuickCheck.Common
import PlutusCore.Generators.QuickCheck.ShrinkTypes
import PlutusCore.Generators.QuickCheck.Substitutions
import PlutusCore.Generators.QuickCheck.Utils

import PlutusCore.Builtin
import PlutusCore.Data
import PlutusCore.Default
import PlutusCore.MkPlc (mkConstant, mkConstantOf, mkTyBuiltin)
import PlutusCore.Name
import PlutusCore.Pretty
import PlutusCore.Subst (typeSubstClosedType)
import PlutusIR
import PlutusIR.Subst

import Data.Bifunctor
import Data.Either
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Proxy
import Data.Set qualified as Set
import Data.Set.Lens (setOf)
import GHC.Stack
import Test.QuickCheck (shrinkList)

addTmBind :: Binding TyName Name DefaultUni DefaultFun ()
          -> Map Name (Type TyName DefaultUni ())
          -> Map Name (Type TyName DefaultUni ())
addTmBind (TermBind _ _ (VarDecl _ x a) _) = Map.insert x a
addTmBind (DatatypeBind _ dat)             = (Map.fromList (matchType dat : constrTypes dat) <>)
addTmBind _                                = id

shrinkConstant :: DefaultUni (Esc a) -> a -> [Term TyName Name DefaultUni DefaultFun ()]
shrinkConstant uni x =
    map (mkConstantOf () uni) $ bring (Proxy @ArbitraryBuiltin) uni $ shrinkBuiltin x

scopeCheckTyVars :: TypeCtx
                 -> (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
                 -> Bool
scopeCheckTyVars tyctx (ty, tm) = setOf ftvTy ty `Set.isSubsetOf` inscope
  where
    inscope = Map.keysSet tyctx <> Set.fromList (map fst $ datatypes tm)

-- | Try to find a variable of type `forall x. x` in the context.
findHelp :: Map Name (Type TyName DefaultUni ()) -> Maybe Name
findHelp ctx =
  case Map.toList $ Map.filter isHelpType ctx of
    []         -> Nothing
    (x, _) : _ -> Just x
  where
    isHelpType (TyForall _ x (Type ()) (TyVar _ x')) = x == x'
    isHelpType _                                     = False

mkHelp :: Map Name (Type TyName DefaultUni ())
       -> Type TyName DefaultUni ()
       -> Term TyName Name DefaultUni DefaultFun ()
mkHelp _ (TyBuiltin _ b)          = minimalBuiltin b
mkHelp (findHelp -> Just help) ty = TyInst () (Var () help) ty
mkHelp _ ty                       = Error () ty

-- | Try to take a term from an old context to a new context and a new type.
-- If we can't do the new type we might return a different type.
fixupTerm_ :: TypeCtx
           -> Map Name (Type TyName DefaultUni ())
           -> TypeCtx
           -> Map Name (Type TyName DefaultUni ())
           -> Type TyName DefaultUni ()
           -> Term TyName Name DefaultUni DefaultFun ()
           -> (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
fixupTerm_ tyctxOld ctxOld tyctxNew ctxNew tyNew tm0 =
  case inferTypeInContext tyctxNew ctxNew tm0 of
    Left _ -> case tm0 of
      LamAbs _ x a tm | TyFun () _ b <- tyNew -> bimap (TyFun () a) (LamAbs () x a)
                                              $ fixupTerm_ tyctxOld (Map.insert x a ctxOld)
                                                           tyctxNew (Map.insert x a ctxNew) b tm
      Apply _ (Apply _ (TyInst _ (Builtin _ Trace) _) s) tm ->
        let (ty', tm') = fixupTerm_ tyctxOld ctxOld tyctxNew ctxNew tyNew tm
        in (ty', Apply () (Apply () (TyInst () (Builtin () Trace) ty') s) tm')
      _ | TyBuiltin _ b <- tyNew -> (tyNew, minimalBuiltin b)
        | otherwise -> (tyNew, mkHelp ctxNew tyNew)
    Right ty -> (ty, tm0)

-- | Try to take a term from an old context to a new context and a new type - default to `mkHelp`.
fixupTerm :: TypeCtx
          -> Map Name (Type TyName DefaultUni ())
          -> TypeCtx
          -> Map Name (Type TyName DefaultUni ())
          -> Type TyName DefaultUni ()
          -> Term TyName Name DefaultUni DefaultFun ()
          -> Term TyName Name DefaultUni DefaultFun ()
fixupTerm _ _ tyctxNew ctxNew tyNew tm
  | isRight (typeCheckTermInContext tyctxNew ctxNew tm tyNew) = tm
  | otherwise                                                 = mkHelp ctxNew tyNew

minimalBuiltin :: SomeTypeIn DefaultUni -> Term TyName Name DefaultUni DefaultFun ()
minimalBuiltin (SomeTypeIn uni) = case toSingKind uni of
    SingType -> mkConstantOf () uni $ go uni
    _        -> error "Higher-kinded built-in types cannot be used here"
  where
    go :: DefaultUni (Esc a) -> a
    go DefaultUniUnit                                                   = ()
    go DefaultUniInteger                                                = 0
    go DefaultUniBool                                                   = False
    go DefaultUniString                                                 = ""
    go DefaultUniByteString                                             = ""
    go DefaultUniData                                                   = I 0
    go (DefaultUniProtoList `DefaultUniApply` _)                        = []
    go (DefaultUniProtoPair `DefaultUniApply` a `DefaultUniApply` b)    = (go a, go b)
    go (f  `DefaultUniApply` _ `DefaultUniApply` _ `DefaultUniApply` _) = noMoreTypeFunctions f

shrinkBind :: HasCallStack
           => Recursivity
           -> TypeCtx
           -> Map Name (Type TyName DefaultUni ())
           -> Binding TyName Name DefaultUni DefaultFun ()
           -> [Binding TyName Name DefaultUni DefaultFun ()]
shrinkBind _ tyctx ctx bind =
  case bind of
    -- Note: this is a bit tricky for recursive binds, if we change a recursive bind we need to
    -- fixup all the other binds in the block. Currently we do this with a fixupTerm_ in the
    -- structural part of shrinking.  In the future this can be made better if we find properties
    -- where lets don't shrink well enough to be understandable.
    TermBind _ s (VarDecl _ x ty) tm -> [ TermBind () s (VarDecl () x ty') tm'
                                        | (ty', tm') <- shrinkTypedTerm tyctx ctx (ty, tm)
                                        ] ++
                                        [ TermBind () Strict (VarDecl () x ty) tm | s == NonStrict ]
    -- These cases are basically just structural
    TypeBind _ (TyVarDecl _ a k) ty  -> [ TypeBind () (TyVarDecl () a k') ty'
                                        | (k', ty') <- shrinkKindAndType tyctx (k, ty) ]
    DatatypeBind _ dat               -> [ DatatypeBind () dat' | dat' <- shrinkDat tyctx dat ]

shrinkDat :: TypeCtx
          -> Datatype TyName Name DefaultUni ()
          -> [Datatype TyName Name DefaultUni ()]
shrinkDat ctx (Datatype _ dd@(TyVarDecl _ d _) xs m cs) =
  [ Datatype () dd xs m cs' | cs' <- shrinkList shrinkCon cs ]
  where
    ctx' = ctx <> Map.fromList [ (x, k) | TyVarDecl _ x k <- xs ]
    shrinkCon (VarDecl _ c ty) = [ VarDecl () c ty''
                                 | ty' <- shrinkType ctx' ty
                                 , let ty'' = setTarget (getTarget ty) ty'
                                 , ty'' /= ty
                                 , d `Set.notMember` setOf ftvTy (setTarget (mkTyBuiltin @_ @() ()) ty') ]
      where
        getTarget (TyFun _ _ b) = getTarget b
        getTarget b             = b
        setTarget t (TyFun _ a b) = TyFun () a (setTarget t b)
        setTarget t _             = t

{-
TODO: Note

nonstructural cases for

    let x1 = y1
        x2 = y2
    in b

1. drop all bindings
2. drop body and pick one binding as a new body and drop all bindings appearing after it
3. drop a single binding if there are more than one (because we handled a single one in 1)
-}

{-
TODO: Note

document terms giving duplicate shrinks like

a -> a
let x = "abc" in "abc"
let x = "abc" in x
(\a1_1 -> a1_1) unit
-}

-- | Shrink a typed term in a type and term context.
-- NOTE: if you want to understand what's going on in this function it's a good
-- idea to look at how we do this for types first (it's a lot simpler).
shrinkTypedTerm :: HasCallStack
                => TypeCtx
                -> Map Name (Type TyName DefaultUni ())
                -> (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
                -> [(Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())]
shrinkTypedTerm tyctx0 ctx0 (ty0, tm0) = concat
    [ -- TODO: this somehow contributes a huge number of duplicates as reported by the @numShrink@
      -- test. How come? Is it because it's called from 'shrinkBind'? Do we even need this kind of
      -- shrinking?
      filter (scopeCheckTyVars tyctx0)
        [ (ty', tm')
        | not $ isHelp ctx0 tm0
        , ty' <- ty0 : shrinkType (tyctx0 <> Map.fromList (datatypes tm0)) ty0
        , let tm' = mkHelp ctx0 ty'
        ]
    , go tyctx0 ctx0 (ty0, tm0)
    ]
  where
    isHelp _ (Constant _ _)           = True
    isHelp ctx (TyInst _ (Var _ x) _) = Just x == findHelp ctx
    isHelp _ (Error _ _)              = True
    isHelp _ _                        = False

    addTyBind (TypeBind _ (TyVarDecl _ a k) _)                      = Map.insert a k
    addTyBind (DatatypeBind _ (Datatype _ (TyVarDecl _ a k) _ _ _)) = Map.insert a k
    addTyBind _                                                     = id

    addTyBindSubst (TypeBind _ (TyVarDecl _ a _) ty) = Map.insert a ty
    addTyBindSubst _                                 = id

    go :: HasCallStack => _
    go tyctx ctx (ty, tm) =
      filter (scopeCheckTyVars tyctx) $
      nonstructural tyctx ctx (ty, tm) ++
      structural    tyctx ctx (ty, tm)

    -- TODO: what about 'TyInst'?
    -- These are the special cases and "tricks" for shrinking
    nonstructural :: HasCallStack => _
    nonstructural tyctx ctx (ty, tm) =
      case tm of
        -- TODO: shrink Rec to NonRec
        Let _ rec bindsL body -> concat
          [ --
            [ fixupTerm_ tyctxInner ctxInner tyctx ctx ty body
            | let tyctxInner  = foldr addTyBind tyctx bindsL
                  ctxInner    = foldr addTmBind ctx   bindsL
            ]
          , -- Make one of the let-bindings the new body dropping the old body and all the
            -- bindings appearing after the chosen binding (we don't need them, since the whole
            -- 'let' is non-recursive and hence the chosen binding can't reference those appearing
            -- after it).
            [ (letTy, case binds of
                -- If there's no bindings before the chosen one, we don't recreate the 'let'.
                []   -> letTm
                b:bs -> Let () NonRec (b :| bs) letTm)
            | (NonEmptyContext binds _, TermBind _ _ (VarDecl _ _ letTy) letTm) <-
                oneHoleContexts bindsL
            , rec == NonRec
              -- TODO: check that the body is not one of the bound variables?
            ]
          , -- Drop a single binding.
            [ second (Let () rec (b :| binds'))
              $ fixupTerm_ tyctxInner ctxInner tyctxInner' ctxInner' ty body
            | (NonEmptyContext binds0 binds1, _) <- oneHoleContexts bindsL,
              let tyctxInner  = foldr addTyBind tyctx bindsL
                  ctxInner    = foldr addTmBind ctx   bindsL
                  binds       = binds0 ++ binds1
                  tyctxInner' = foldr addTyBind tyctx binds
                  ctxInner'   = foldr addTmBind ctx   binds
            , b:binds' <- [binds]
            ]
          ]

        LamAbs _ x a body ->
          [ fixupTerm_ tyctx (Map.insert x a ctx) tyctx ctx b body
          | TyFun _ _ b <- [ty]
          ]

        Apply _ fun arg | Right argTy <- inferTypeInContext tyctx ctx arg ->
          -- Drop substerms
          [(argTy, arg), (TyFun () argTy ty, fun)]

        TyAbs _ x _ body ->
          [ fixupTerm_ (Map.insert x k tyctx) ctx tyctx ctx tyInner' body
          | TyForall _ y k tyInner <- [ty]
          , let tyInner' = typeSubstClosedType y (minimalType k) tyInner
          ]

        -- Builtins can shrink to unit. More fine-grained shrinking is in `structural` below.
        Constant _ (Some (ValueOf uni _)) -> case uni of
            DefaultUniUnit -> []
            _              -> [(mkTyBuiltin @_ @() (), mkConstant () ())]

        _ -> []

    -- These are the structural (basically homomorphic) cases in shrinking.
    -- They all just try to shrink a single subterm at a time. We also
    -- use fixupTerm to adjust types here in a trick similar to how we shrunk
    -- types above.
    structural :: HasCallStack => _
    structural tyctx ctx (ty, tm) =
      case tm of

        -- TODO: this needs a long, long Note...
        Let _ rec binds body ->
          [ (substTypeParallel subst ty', Let () rec binds body')
          | (ty', body') <- go tyctxInner ctxInner (ty, body) ] ++
          [ fix $ second (Let () rec binds') $
                fixupTerm_ tyctxInner ctxInner tyctxInner' ctxInner' ty body
            | (context@(NonEmptyContext before _), bind) <- oneHoleContexts binds,
              let ctxBind | Rec <- rec = ctxInner
                          | otherwise  = foldr addTmBind ctx before
                  tyctxBind | Rec <- rec = tyctxInner
                            | otherwise  = foldr addTyBind tyctx before,
              bind' <- shrinkBind rec tyctxBind ctxBind bind,
              let binds'      = plugHole context bind'
                  tyctxInner' = foldr addTyBind tyctx binds'
                  ctxInner'   = foldr addTmBind ctx   binds'
                  fix = uncurry (fixupTerm_ tyctx ctx tyctx ctx)
          ] where subst = foldr addTyBindSubst mempty binds
                  tyctxInner = foldr addTyBind tyctx binds
                  ctxInner   = foldr addTmBind ctx binds

        -- TODO: shrink the function too!
        TyInst _ fun argTy -> case inferTypeInContext tyctx ctx fun of
          Right (TyForall _ x k tyInner) ->
            [ (substType (Map.singleton x argTy') tyInner', TyInst () fun' argTy')
            | (k', argTy') <- shrinkKindAndType tyctx (k, argTy)
            , let tyInner' | k == k'   = tyInner
                           -- TODO: use proper fixupType
                           | otherwise = substType (Map.singleton x $ minimalType k) tyInner
                  fun' = fixupTerm tyctx ctx tyctx ctx (TyForall () x k' tyInner') fun
            ]
          Left err -> error $ displayPlcCondensedErrorClassic err
          Right tyWrong -> error $ "Expected a 'TyForall', but got " ++ displayPlcDef tyWrong

        -- TODO: shrink the kind too like with the type in @LamAbs@ below.
        TyAbs _ x _ body | not $ Map.member x tyctx ->
          [ (TyForall () x k tyInner', TyAbs () x k body')
          | TyForall _ y k tyInner <- [ty]
          , (tyInner', body') <- go (Map.insert x k tyctx) ctx (renameVar y x tyInner, body)
          ]

        LamAbs _ x a body ->
          [ (TyFun () a b', LamAbs () x a body')
          | TyFun _ _ b <- [ty],
            (b', body') <- go tyctx (Map.insert x a ctx) (b, body)
          ] ++
          [ bimap (TyFun () a') (LamAbs () x a') $
              fixupTerm_ tyctx (Map.insert x a ctx) tyctx (Map.insert x a' ctx) b body
          | TyFun _ _ b <- [ty],
            a' <- shrinkType tyctx a
          ]

        Apply _ fun arg -> case inferTypeInContext tyctx ctx arg of
          Left err    -> error err
          Right argTy ->
            [ (ty', Apply () fun' arg')
            | (TyFun _ argTy' ty', fun') <- go tyctx ctx (TyFun () argTy ty, fun)
            , let arg' = fixupTerm tyctx ctx tyctx ctx argTy' arg
            ] ++
            [ (ty,  Apply () fun' arg')
            | (argTy', arg') <- go tyctx ctx (argTy, arg)
            , let fun' = fixupTerm tyctx ctx tyctx ctx (TyFun () argTy' ty) fun
            ]

        Constant _ (Some (ValueOf uni x)) -> map ((,) ty) $ shrinkConstant uni x

        -- TODO: handle all the cases explicitly.
        _ -> []

shrinkClosedTypedTerm :: (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
                      -> [(Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())]
shrinkClosedTypedTerm = shrinkTypedTerm mempty mempty
