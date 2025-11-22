{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

{-| This module defines the type shrinker. The shrinking order isn't specified, so the shrinker
may or may not behave correctly, we don't really know. If shrinking ever loops, feel free to kill
this module or reverse-engineer the shrinker and fix the problem. -}
module PlutusCore.Generators.QuickCheck.ShrinkTypes where

import PlutusCore.Generators.QuickCheck.Builtin
import PlutusCore.Generators.QuickCheck.Common
import PlutusCore.Generators.QuickCheck.GenTm
import PlutusCore.Generators.QuickCheck.GenerateKinds

import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.Default
import PlutusCore.Name.Unique
import PlutusCore.Pretty
import PlutusCore.Subst

import Data.Map.Strict qualified as Map
import Data.Set.Lens (setOf)
import GHC.Stack
import Test.QuickCheck.Arbitrary

{- Note [Avoiding Shrinking Loops]

   Shrinking loops can be tricky to deal with and unfortunately there is no
   golden rule for how to avoid them. However, one good strategy to avoid them
   is to make sure shrinking isn't doing anything too clever. As a general set of
   rules:
   * Don't do "special case" shrinking that trades off size in one subterm for size
     in a different subterm. For example, it's generally dangerous to shrink
     `Node (Node Leaf (Node Leaf Leaf)) (Node Leaf Leaf)` to
     `Node Leaf (Node Leaf (Node Leaf Leaf))` even though the number of leaves is
     decreasing unless you've explicitly made "the number of leaves decreases" the
     measure by which you're shrinking (in which case you need to have a property for
     this!)
   * Carefully guard base cases - the shrinker
     `shrink tree = Leaf : someCleverShrinkingStrategy` will loop, while
     `shrink tree = [ Leaf | tree /= Leaf ] ++ someCleverShrinkingStrategy` will not.
     You will see this kind of thing used below wherever we use `minimalType` and `mkHelp`
     in the shrinkers.
   * Write properties to test your shrinkers and *run them when you change your shrinkers*.
     See e.g. `prop_noTermShrinkLoops` in module `GeneratorSpec`.
-}

-- Note that compared to 'genAtomicType' this one for, say, @* -> * -> *@ always gives @pair@, while
-- 'genAtomicType' can give you a type variable, 'pair' or a type lambda returning a type variable,
-- 'list' or a type lambda returning a type variable or a built-in type of kind @*@.
{-| Give a unique "least" (intentionally vaguely specified by "shrinking order")
type of that kind. Note: this function requires care and attention to not get
a shrinking loop. If you think you need to mess with this function:
0. First, you *must* read the note Note [Avoiding Shrinking Loops]
1. You're probably wrong, think again and
2. If you're sure you're not wrong you need to be very careful and
   test the shrinking to make sure you don't get in a loop.
3. Finally, you *must* read the note Note [Avoiding Shrinking Loops] -}
minimalType :: Kind () -> Type TyName DefaultUni ()
minimalType = go . argsFunKind
  where
    go = \case
      [] -> unit
      [Type {}] -> list
      [Type {}, Type {}] -> pair
      k : ks -> TyLam () (TyName $ Name "_" (toEnum 0)) k $ go ks

    unit = mkTyBuiltin @_ @() ()
    list = mkTyBuiltin @_ @[] ()
    pair = mkTyBuiltin @_ @(,) ()

{-| Take a type in a context and a target kind and try adjust the type to have the target kind.
If can't make the adjusting successful, return the 'minimalType' of the target kind.
Precondition: new kind is smaller or equal to old kind of the type.
Complies with the implicit shrinking order.
TODO (later): also allow changing which context it's valid in -}
fixKind
  :: HasCallStack
  => TypeCtx
  -> Type TyName DefaultUni ()
  -> Kind ()
  -> Type TyName DefaultUni ()
fixKind ctx ty k
  -- Nothing to do if we already have the right kind
  | origK == k = ty
  | not $ k `leKind` origK =
      error $
        concat
          [ "Internal error. New kind: "
          , display k
          , "\nis not smaller than the old one: "
          , display $ unsafeInferKind ctx ty
          ]
  | otherwise = case ty of
      -- Switch a variable out for a different variable of the right kind
      TyVar _ _ -> case [y | (y, k') <- Map.toList ctx, k == k'] of
        y : _ -> TyVar () y
        _ -> minimalType k
      -- Try to fix application by fixing the function
      TyApp _ a b -> TyApp () (fixKind ctx a $ KindArrow () (unsafeInferKind ctx b) k) b
      TyLam _ x kx b ->
        case k of
          -- Fix lambdas to * by substituting a minimal type for the argument
          -- and fixing the body.
          Type {} -> fixKind ctx (typeSubstClosedType x (minimalType kx) b) k
          -- Fix functions by either keeping the argument around (if we can) or getting
          -- rid of the argument (by turning its use-sites into minimal types) and introducing
          -- a new argument.
          KindArrow _ ka kb
            | ka == kx -> TyLam () x kx $ fixKind (Map.insert x kx ctx) b kb
            | not $ kb `leKind` kb' -> error "fixKind"
            | otherwise -> TyLam () x ka $ fixKind ctx' b' kb
            where
              ctx' = Map.insert x ka ctx
              b' = typeSubstClosedType x (minimalType kx) b
              kb' = unsafeInferKind ctx' b'
      -- Ill-kinded builtins just go to minimal types
      TyBuiltin {} -> minimalType k
      -- Unreachable, because the target kind must be less than or equal to the original kind. We
      -- handled the case where they are equal at the beginning of the function, so at this point the
      -- target kind must be strictly less than the original kind, but for these types we know the
      -- original kind is @*@, and there is no kind smaller than that.
      TyFun {} -> error "Internal error: unreachable clause."
      TyIFix {} -> error "Internal error: unreachable clause."
      TyForall {} -> error "Internal error: unreachable clause."
      TySOP {} -> error "Internal error: unreachable clause."
  where
    origK = unsafeInferKind ctx ty

{-| Shrink a well-kinded type in a context to new types, possibly with new kinds.
The new kinds are guaranteed to be smaller than or equal to the old kind.
TODO: also shrink to new context
      need old context and new context -}
shrinkKindAndType
  :: HasCallStack
  => TypeCtx
  -> (Kind (), Type TyName DefaultUni ())
  -> [(Kind (), Type TyName DefaultUni ())]
shrinkKindAndType ctx (k0, ty) =
  let minK0 = minimalType k0
   in -- If we are not already minimal, add the minial type as a possible shrink.
      ([(k0, m) | let m = minimalType k0, m /= ty] ++) . filter ((/= minK0) . snd) $
        [(k, m) | k <- shrink k0, let m = minimalType k]
          ++ case ty of
            -- Variables shrink to arbitrary "smaller" variables
            -- Note: the order on variable names here doesn't matter,
            -- it's just because we need *some* order or otherwise
            -- shrinking doesn't terminate.
            TyVar _ x ->
              [ (ky, TyVar () y)
              | (y, ky) <- Map.toList ctx
              , ltKind ky k0 || ky == k0 && y < x
              ]
            -- Functions shrink to either side of the arrow and both sides
            -- of the arrow shrink independently.
            TyFun _ a b ->
              map (Type (),) $
                concat
                  [
                    [ a
                    , b
                    ]
                  , [ TyFun () a' b
                    | a' <- shrinkType ctx a
                    ]
                  , [ TyFun () a b'
                    | b' <- shrinkType ctx b
                    ]
                  ]
            -- This case needs to be handled with a bit of care. First we shrink applications by
            -- doing simple stuff like shrinking the function and body separately when we can.
            -- The slightly tricky case is the concat trace. See comment below.
            TyApp _ f a ->
              concat
                [ [ (ka, a)
                  | ka `leKind` k0
                  ]
                , [ (k0, typeSubstClosedType x m b)
                  | TyLam _ x _ b <- [f]
                  , let m = minimalType ka
                  , m /= a -- @m == a@ is handled right below.
                  ]
                , [ (k0, typeSubstClosedType x a b)
                  | TyLam _ x _ b <- [f]
                  , null (setOf ftvTy a)
                  ]
                , -- Here we try to shrink the function f, if we get something whose kind
                  -- is small enough we can return the new function f', otherwise we
                  -- apply f' to `fixKind ctx a ka'` - which takes `a` and tries to rewrite it
                  -- to something of kind `ka'`.
                  concat
                    [ case kf' of
                        Type {} ->
                          [ (kf', f')
                          | f' /= a -- @f' == a@ is handled above.
                          ]
                        KindArrow _ ka' kb' ->
                          [ (kb', TyApp () f' (fixKind ctx a ka'))
                          | leKind kb' k0
                          , leKind ka' ka
                          ]
                    | (kf', f') <- shrinkKindAndType ctx (KindArrow () ka k0, f)
                    ]
                , -- Here we shrink the argument and fixup the function to have the right kind.
                  [ (k0, TyApp () (fixKind ctx f (KindArrow () ka' k0)) a')
                  | (ka', a') <- shrinkKindAndType ctx (ka, a)
                  ]
                ]
              where
                ka = unsafeInferKind ctx a
            -- type lambdas shrink by either shrinking the kind of the argument or shrinking the body
            TyLam _ x ka b ->
              concat
                [ -- We can simply get rid of the binding by instantiating the variable.

                  [ (kb, typeSubstClosedType x (minimalType ka) b)
                  ]
                , -- We could've used @fixKind (Map.insert x ka' ctx) (TyVar () x) ka)@ here instead of
                  -- @minimalType ka@, so that the usages of @x@ are preserved when possible, but that would
                  -- mean fixing a kind to a bigger one (because @ka'@ has to be smaller than @ka@ and we'd go
                  -- in the opposite direction), which is not supported by 'fixKind' (even though just
                  -- commenting out the relevant check and making the change here does seem to give us
                  -- better shrinking that still properly terminates, 'cause why would it not).
                  [ (KindArrow () ka' kb, TyLam () x ka' $ typeSubstClosedType x (minimalType ka) b)
                  | ka' <- shrink ka
                  ]
                , [ (KindArrow () ka kb', TyLam () x ka b')
                  | (kb', b') <- shrinkKindAndType (Map.insert x ka ctx) (kb, b)
                  ]
                ]
              where
                kb = case k0 of
                  KindArrow _ _ k' -> k'
                  _ ->
                    error $ "Internal error: " ++ display k0 ++ " is not a 'KindArrow'"
            TyForall _ x ka b ->
              map (Type (),) $
                concat
                  [ -- We can simply get rid of the binding by instantiating the variable.

                    [ typeSubstClosedType x (minimalType ka) b
                    ]
                  , -- We can always just shrink the bound variable to a smaller kind and ignore it
                    -- Similarly to 'TyLam', we could've used 'fixKind' here, but we don't do it for the same
                    -- reason.
                    [ TyForall () x ka' $ typeSubstClosedType x (minimalType ka) b
                    | ka' <- shrink ka
                    ]
                  , [ TyForall () x ka b'
                    | -- or we shrink the body.
                    b' <- shrinkType (Map.insert x ka ctx) b
                    ]
                  ]
            TyBuiltin _ someUni ->
              [ (kindOfBuiltinType uni', TyBuiltin () $ SomeTypeIn uni')
              | SomeTypeIn uni' <- shrinkBuiltinType someUni
              ]
            TyIFix _ pat arg ->
              map (Type (),) $
                concat
                  [
                    [ fixKind ctx pat $ Type ()
                    , fixKind ctx arg $ Type ()
                    ]
                  , [ TyIFix () pat' (fixKind ctx arg kArg')
                    | (kPat', pat') <- shrinkKindAndType ctx (toPatFuncKind kArg, pat)
                    , Just kArg' <- [fromPatFuncKind kPat']
                    ]
                  , [ TyIFix () (fixKind ctx pat $ toPatFuncKind kArg') arg'
                    | (kArg', arg') <- shrinkKindAndType ctx (kArg, arg)
                    ]
                  ]
              where
                kArg = unsafeInferKind ctx arg
            TySOP _ tyls ->
              map (Type (),) $
                concat
                  [ -- Shrink to any type within the SOP.
                    concat tyls
                  , -- Shrink either the entire sum or a product within it or a type within a product.
                    TySOP () <$> shrinkList (shrinkList $ shrinkType ctx) tyls
                  ]

-- | Shrink a type in a context assuming that it is of kind *.
shrinkType
  :: HasCallStack
  => TypeCtx
  -> Type TyName DefaultUni ()
  -> [Type TyName DefaultUni ()]
shrinkType ctx ty = map snd $ shrinkKindAndType ctx (Type (), ty)

-- | Shrink a type of a given kind in a given context in a way that keeps its kind
shrinkTypeAtKind
  :: HasCallStack
  => TypeCtx
  -> Kind ()
  -> Type TyName DefaultUni ()
  -> [Type TyName DefaultUni ()]
-- It is unfortunate that we need to produce all those shrunk types just to filter out a lot of them
-- afterwards. But we still should get good coverage in the end.
shrinkTypeAtKind ctx k ty = [ty' | (k', ty') <- shrinkKindAndType ctx (k, ty), k == k']
