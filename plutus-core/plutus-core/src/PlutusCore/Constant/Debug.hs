{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module helps to visualize and debug the 'TypeScheme' inference machinery from the
-- @Meaning@ module.
module PlutusCore.Constant.Debug where

import PlutusCore.Constant.Meaning
import PlutusCore.Constant.Typed
import PlutusCore.Core
import PlutusCore.Default.Universe
import PlutusCore.Name

data FunDebug
type TermDebug = Term TyName Name DefaultUni FunDebug ()

-- | Instantiate type variables in the type of a value using 'EnumerateFromTo'.
-- This function only performs the enumeration and checks that the result does not have certain
-- constraints, so it's allowed for the type to reference types that are not in the universe.
-- Example usages:
--
-- >>> :t enumerateDebug False
-- enumerateDebug False :: Bool
-- >>> :t enumerateDebug $ Just 'a'
-- <interactive>:1:1-25: error:
--     • Ambiguous type variable ‘j0’ arising from a use of ‘enumerateDebug’
--       prevents the constraint ‘(HandleSpecialCasesEnter
--                                   0
--                                   j0
--                                   (PlutusCore.Constant.Typed.ReverseGo
--                                      '[] (AsSpineRev (Maybe Char))))’ from being solved.
--       Probable fix: use a type annotation to specify what ‘j0’ should be.
--       These potential instances exist:
--         four instances involving out-of-scope types
--         (use -fprint-potential-instances to see them all)
--     • In the expression: enumerateDebug $ Just 'a'
-- >>> :t enumerateDebug $ \_ -> ()
-- enumerateDebug $ \_ -> ()
--   :: Opaque
--        (Term TyName Name DefaultUni FunDebug ())
--        (TyVarRep ('TyNameRep "a" 0))
--      -> ()
-- >>> :t enumerateDebug 42
-- <interactive>:1:16-17: error:
--     • Built-in functions are not allowed to have constraints
--       To fix this error instantiate all constrained type variables
--     • In the first argument of ‘enumerateDebug’, namely ‘42’
--       In the expression: enumerateDebug 42
enumerateDebug :: forall a j. EnumerateFromTo 0 j TermDebug a => a -> a
enumerateDebug = id

-- >>> :t enumerateDebug (undefined :: Opaque term (a, b))
-- enumerateDebug (undefined :: Opaque term (a, b))
--   :: Opaque
--        term (TyVarRep ('TyNameRep "a" 0), TyVarRep ('TyNameRep "b" 1))
-- >>> :t enumerateDebug (undefined :: Opaque term a)
-- enumerateDebug (undefined :: Opaque term a)
--   :: Opaque
--        (Term TyName Name DefaultUni FunDebug ())
--        (TyVarRep ('TyNameRep "a" 0))
-- >>> :t enumerateDebug (undefined :: SomeConstant uni a)
-- enumerateDebug (undefined :: SomeConstant uni a)
--   :: SomeConstant uni (TyVarRep ('TyNameRep "a" 0))
-- >>> :t enumerateDebug (undefined :: SomeConstant uni a -> SomeConstant uni b)
-- enumerateDebug (undefined :: SomeConstant uni a -> SomeConstant uni b)
--   :: SomeConstant uni (TyVarRep ('TyNameRep "a" 0))
--      -> SomeConstant uni (TyVarRep ('TyNameRep "b" 1))

-- >>> import PlutusCore.Evaluation.Result
-- >>> :t enumerateDebug (undefined :: SomeConstant uni a -> EvaluationResult b)
-- enumerateDebug (undefined :: SomeConstant uni a -> EvaluationResult b)
--   :: HandleSpecialCasesEnter
--        1 j (PlutusCore.Constant.Typed.ReverseGo '[] (AsSpineRev b)) =>
--      SomeConstant uni (TyVarRep ('TyNameRep "a" 0))
--      -> EvaluationResult b


--          fstPlc :: Opaque term (a, b) -> EvaluationResult (Opaque term a)

-- >>> enumerateDebug (undefined :: Opaque term (a, b)) `seq` ()
-- <interactive>:331:2-49: error:
--     • '(Opaque term0 (a0, b0), '[AnyRep (a0, b0)])
--     • In the first argument of ‘seq’, namely
--         ‘enumerateDebug (undefined :: Opaque term (a, b))’
--       In the expression:
--         enumerateDebug (undefined :: Opaque term (a, b)) `seq` ()
--       In an equation for ‘it’:
--           it = enumerateDebug (undefined :: Opaque term (a, b)) `seq` ()

-- >>> :t inferDebug (undefined :: SomeConstant uni a)
-- inferDebug (undefined :: SomeConstant uni a)
--   :: SomeConstant DefaultUni (TyVarRep ('TyNameRep "a" 0))

-- >>> import Data.Proxy
-- >>> :set -XDataKinds
-- >>> :t toTypeAst @_ @DefaultUni $ Proxy @(RepInfer (TyVarRep ('TyNameRep "a" 0)))
-- <interactive>:1:1-74: error:
--     • Ambiguous type variable ‘a0’ arising from a use of ‘toTypeAst’
--       prevents the constraint ‘(KnownTypeAst
--                                   DefaultUni
--                                   (RepInfer (TyVarRep ('TyNameRep "a" 0))))’ from being solved.
--       Probable fix: use a type annotation to specify what ‘a0’ should be.
--       These potential instance exist:
--         one instance involving out-of-scope types
--         (use -fprint-potential-instances to see them all)
--     • In the expression:
--         toTypeAst @_ @DefaultUni
--           $ Proxy @(RepInfer (TyVarRep ('TyNameRep "a" 0)))

-- >>> import Data.Proxy
-- >>> :set -XDataKinds
-- >>> toTypeAst $ Proxy @(SomeConstant DefaultUni (TyVarRep ('TyNameRep "a" 0)))
-- TyVar () (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 0}}})

-- >>> :t inferDebug (Prelude.id :: Opaque term (TyAppRep a Integer) -> Opaque term (TyAppRep a Integer))
-- <interactive>:1:1-95: error:
--     • No instance for (KnownTypeAst
--                          DefaultUni (RepInfer (TyVarRep ('TyNameRep "a" 0))))
--         arising from a use of ‘inferDebug’
--     • In the expression:
--         inferDebug
--           (id ::
--              Opaque term (TyAppRep a Integer)
--              -> Opaque term (TyAppRep a Integer))


-- >>> :set -XTypeApplications
-- >>> :t (Proxy @(AsSpine (a, b)))
-- <interactive>:1:19: error: Not in scope: type variable ‘a’
-- <interactive>:1:22: error: Not in scope: type variable ‘b’

-- Opaque (SomeValueOf uni) (a, b) ?

-- >>> :t inferDebug (undefined :: Opaque term (a, b))
-- <interactive>:1:1-44: error:
--     • No instance for (Contains DefaultUni TyVarRep)
--         arising from a use of ‘inferDebug’
--     • In the expression: inferDebug (undefined :: Opaque term (a, b))
-- >>> :t inferDebug (undefined :: Opaque term a)
-- inferDebug (undefined :: Opaque term a)
--   :: Opaque
--        (Term TyName Name DefaultUni FunDebug ())
--        (TyVarRep ('TyNameRep "a" 0))
-- >>> :t inferDebug (undefined :: SomeConstant uni a)
-- inferDebug (undefined :: SomeConstant uni a)
--   :: (KnownPolytype
--         (Merge (ToBinds f) (ListToBinds args))
--         TermDebug
--         '[]
--         (SomeConstant DefaultUni a)
--         (SomeConstant DefaultUni a),
--       HandleSpecialCasesEnter
--         0 j (PlutusCore.Constant.Typed.ReverseGo '[] (AsSpineRev a)),
--       KnownTypeAst DefaultUni f,
--       Data.SOP.Constraint.All (KnownTypeAst DefaultUni) args,
--       PlutusCore.Constant.Typed.ReverseGo '[] (AsSpineRev a)
--       ~ (f : args),
--       ListToBinds
--         (PlutusCore.Constant.Typed.ReverseGo '[] (AsSpineRev a))
--       ~ Merge (ToBinds f) (ListToBinds args)) =>
--      SomeConstant DefaultUni a
-- >>> :t inferDebug (undefined :: SomeConstant uni a -> SomeConstant uni b)
-- inferDebug (undefined :: SomeConstant uni a -> SomeConstant uni b)
--   :: (KnownPolytype
--         (Merge
--            (Merge
--               (ListToBinds
--                  (PlutusCore.Constant.Typed.ReverseGo '[] (AsSpineRev a)))
--               '[])
--            (ListToBinds
--               (PlutusCore.Constant.Typed.ReverseGo '[] (AsSpineRev b))))
--         TermDebug
--         '[SomeConstant DefaultUni a]
--         (SomeConstant DefaultUni b)
--         (SomeConstant DefaultUni a -> SomeConstant DefaultUni b),
--       HandleSpecialCasesEnter
--         k j (PlutusCore.Constant.Typed.ReverseGo '[] (AsSpineRev b)),
--       HandleSpecialCasesEnter
--         0 k (PlutusCore.Constant.Typed.ReverseGo '[] (AsSpineRev a)),
--       KnownTypeAst DefaultUni f1, KnownTypeAst DefaultUni f2,
--       Data.SOP.Constraint.All (KnownTypeAst DefaultUni) args1,
--       Data.SOP.Constraint.All (KnownTypeAst DefaultUni) args2,
--       PlutusCore.Constant.Typed.ReverseGo '[] (AsSpineRev b)
--       ~ (f2 : args2),
--       PlutusCore.Constant.Typed.ReverseGo '[] (AsSpineRev a)
--       ~ (f1 : args1)) =>
--      SomeConstant DefaultUni a -> SomeConstant DefaultUni b


-- | Instantiate type variables in the type of a value using 'EnumerateFromTo' and check that it's
-- possibe to construct a 'TypeScheme' out of the resulting type. Example usages:
--
-- >>> :t inferDebug False
-- inferDebug False :: Bool
-- >>> :t inferDebug $ Just 'a'
-- <interactive>:1:1-21: error:
--     • No instance for (KnownPolytype
--                          (ToBinds (Maybe Char)) TermDebug '[] (Maybe Char) (Maybe Char))
--         arising from a use of ‘inferDebug’
--     • In the expression: inferDebug $ Just 'a'
-- >>> :t inferDebug $ \_ -> ()
-- inferDebug $ \_ -> ()
--   :: Opaque
--        (Term TyName Name DefaultUni FunDebug ())
--        (TyVarRep ('TyNameRep "a" 0))
--      -> ()
inferDebug
    :: forall a binds args res j.
       ( args ~ GetArgs a, a ~ FoldArgs args res, binds ~ Merge (ListToBinds args) (ToBinds res)
       , KnownPolytype binds TermDebug args res a, EnumerateFromTo 0 j TermDebug a
       , KnownMonotype TermDebug args res a
       )
    => a -> a
inferDebug = id
