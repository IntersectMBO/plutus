{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

-- | This module defines the type shrinker. The shrinking order isn't specified, so the shrinker
-- may or may not behave correctly, we don't really know. If shrinking ever loops, feel free to kill
-- this module or reverse-engineer the shrinker and fix the problem.
module PlutusCore.Generators.PIR.ShrinkTypes where

import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Set.Lens (setOf)
import GHC.Stack

import PlutusCore.Default
import PlutusCore.Generators.PIR.Common
import PlutusCore.MkPlc (mkTyBuiltin)
import PlutusCore.Name
import PlutusCore.Pretty
import PlutusCore.Subst
import PlutusIR

import PlutusCore.Generators.PIR.GenTm
import PlutusCore.Generators.PIR.GenerateKinds

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

-- | Give a unique "least" (intentionally vaguely specified by "shrinking order")
-- type of that kind. Note: this function requires care and attention to not get
-- a shrinking loop. If you think you need to mess with this function:
-- 0. First, you *must* read the note Note [Avoiding Shrinking Loops]
-- 1. You're probably wrong, think again and
-- 2. If you're sure you're not wrong you need to be very careful and
--    test the shrinking to make sure you don't get in a loop.
-- 3. Finally, you *must* read the note Note [Avoiding Shrinking Loops]
minimalType :: Kind () -> Type TyName DefaultUni ()
minimalType = go . argsKind where
  go = \case
    []               -> unit
    [Type{}]         -> list
    [Type{}, Type{}] -> pair
    k:ks             -> TyLam () (TyName $ Name "_" (toEnum 0)) k $ go ks

  unit = mkTyBuiltin @_ @() ()
  list = mkTyBuiltin @_ @[] ()
  pair = mkTyBuiltin @_ @(,) ()

-- | Take a type in a context and a new target kind
--   Precondition: new kind is smaller or equal to old kind of the type.
--   TODO (later): also allow changing which context it's valid in
fixKind :: HasCallStack
        => Map TyName (Kind ())
        -> Type TyName DefaultUni ()
        -> Kind ()
        -> Type TyName DefaultUni ()
fixKind ctx ty k
  -- Nothing to do if we already have the right kind
  | unsafeInferKind ctx ty == k = ty
  | not $ k `leKind` unsafeInferKind ctx ty =
      error "fixKind not smaller"
  | otherwise = case ty of
    -- Switch a variable out for a different variable of the right kind
    TyVar _ _ -> case [y | (y, k') <- Map.toList ctx, k == k'] of
        y : _ -> TyVar () y
        _     -> minimalType k
    -- Try to fix application by fixing the function
    TyApp _ a b -> TyApp () (fixKind ctx a $ KindArrow () (unsafeInferKind ctx b) k) b
    TyLam _ x kx b ->
      case k of
        -- Fix lambdas to * by substituting a minimal type for the argument
        -- and fixing the body.
        Type{} -> fixKind ctx (typeSubstClosedType x (minimalType kx) b) k
        -- Fix functions by either keeping the argument around (if we can) or getting
        -- rid of the argument (by turning its use-sites into minimal types) and introducing
        -- a new argument.
        KindArrow _ ka kb
          | ka == kx              -> TyLam () x kx $ fixKind (Map.insert x kx ctx) b kb
          | not $ kb `leKind` kb' -> error "fixKind"
          | otherwise             -> TyLam () x ka $ fixKind ctx' b' kb
            where
              ctx' = Map.insert x ka ctx
              b'   = typeSubstClosedType x (minimalType kx) b
              kb'  = unsafeInferKind ctx' b'
    -- Ill-kinded builtins just go to minimal types
    TyBuiltin{} -> minimalType k
    _ -> error "fixKind"

-- | Shrink a well-kinded type in a context to new types, possibly with new kinds.
-- The new kinds are guaranteed to be smaller than or equal to the old kind.
-- TODO: also shrink to new context
--       need old context and new context
shrinkKindAndType :: HasCallStack
                  => Map TyName (Kind ())
                  -> (Kind (), Type TyName DefaultUni ())
                  -> [(Kind (), Type TyName DefaultUni ())]
shrinkKindAndType ctx (k0, ty) =
  -- If we are not already minimal, add the minial type as a possible shrink.
  [(k, m) | k <- k0 : shrink k0, let m = minimalType k, m /= ty] ++
  -- TODO: it might be worth-while to refactor this to the structural + nonstructural
  -- style we use below. Unsure if that's more readable. CODE REVIEW: what do you think?
  case ty of
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
    TyFun _ a b -> concat
        [ [ (k0, a), (k0, b)
          ]
        , [ (k0, TyFun () a' b)
          | (_, a') <- shrinkKindAndType ctx (k0, a)
          ]
        , [ (k0, TyFun () a b')
          | (_, b') <- shrinkKindAndType ctx (k0, b)
          ]
        ]
    -- This case needs to be handled with a bit of care. First we shrink applications by
    -- doing simple stuff like shrinking the function and body separately when we can.
    -- The slightly tricky case is the concat trace. See comment below.
    TyApp _ f a -> concat
        [ [ (ka, a)
          | ka `leKind` k0
          ]
        , [ (k0, b)
          | TyLam _ x _ b <- [f], not $ Set.member x (setOf ftvTy b)
          ]
        , [ (k0, typeSubstClosedType x a b)
          | TyLam _ x _ b <- [f], null (setOf ftvTy a)
          ]
        -- Here we try to shrink the function f, if we get something whose kind
        -- is small enough we can return the new function f', otherwise we
        -- apply f' to `fixKind ctx a ka'` - which takes `a` and tries to rewrite it
        -- to something of kind `ka'`.
        , concat
            [ concat
                [ case kf' of
                    Type{}              -> [(kf', f')]
                    KindArrow _ ka' kb' ->
                        [ (kb', TyApp () f' (fixKind ctx a ka'))
                        | leKind kb' k0, leKind ka' ka
                        ]
                | (kf', f') <- shrinkKindAndType ctx (KindArrow () ka k0, f)
                ]
            , -- Here we shrink the argument and fixup the function to have the right kind.
              [ (k0, TyApp () (fixKind ctx f (KindArrow () ka' k0)) a')
              | (ka', a') <- shrinkKindAndType ctx (ka, a)
              ]
            ]
        ]
      where ka = unsafeInferKind ctx a
    -- type lambdas shrink by either shrinking the kind of the argument or shrinking the body
    TyLam _ x ka b -> concat
        [ [ (KindArrow () ka' kb, TyLam () x ka' $ typeSubstClosedType x (minimalType ka) b)
          | ka' <- shrink ka
          ]
        , [ (KindArrow () ka kb', TyLam () x ka b')
          | (kb', b') <- shrinkKindAndType (Map.insert x ka ctx) (kb, b)
          ]
        ]
      where
          kb = case k0 of
              KindArrow _ _ k' -> k'
              _                ->
                  error $ "Internal error: " ++ display k0 ++ " is not a 'KindArrow'"
    TyForall _ x ka b -> concat
        [ -- If the bound variable doesn't matter we get rid of the binding.
          [ (k0, b)
          | not $ Set.member x (setOf ftvTy b)
          ]
        , -- We can always just shrink the bound variable to a smaller kind and ignore it
          [ (k0, TyForall () x ka' $ typeSubstClosedType x (minimalType ka) b)
          | ka' <- shrink ka
          ]
        , [ (k0, TyForall () x ka b')
            -- or we shrink the body.
          | (_, b') <- shrinkKindAndType (Map.insert x ka ctx) (Star, b)
          ]
        ]
    TyBuiltin{}       -> []
    TyIFix _ pat arg  -> concat
        [ [ (Star, fixKind ctx pat Star), (Star, fixKind ctx arg Star)
          ]
        , [ (Star, TyIFix () pat' (fixKind ctx arg kArg'))
          | (kPat', pat') <- shrinkKindAndType ctx (toPatKind kArg, pat),
            Just kArg' <- [fromPatKind kPat']
          ]
        , [ (Star, TyIFix () (fixKind ctx pat $ toPatKind kArg') arg')
          | (kArg', arg') <- shrinkKindAndType ctx (kArg, arg)
          ]
        ]
      where
        kArg = unsafeInferKind ctx arg
        toPatKind k = (k :-> Star) :-> k :-> Star

        fromPatKind ((k1 :-> Star) :-> k2 :-> Star) | k1 == k2 = Just k1
        fromPatKind _                                          = Nothing

-- | Shrink a type in a context assuming that it is of kind *.
shrinkType :: HasCallStack
           => Map TyName (Kind ())
           -> Type TyName DefaultUni ()
           -> [Type TyName DefaultUni ()]
shrinkType ctx ty = map snd $ shrinkKindAndType ctx (Star, ty)

-- | Shrink a type of a given kind in a given context in a way that keeps its kind
shrinkTypeAtKind :: HasCallStack
                 => Map TyName (Kind ())
                 -> Kind ()
                 -> Type TyName DefaultUni ()
                 -> [Type TyName DefaultUni ()]
shrinkTypeAtKind ctx k ty = [ ty' | (k', ty') <- shrinkKindAndType ctx (k, ty), k == k' ]
