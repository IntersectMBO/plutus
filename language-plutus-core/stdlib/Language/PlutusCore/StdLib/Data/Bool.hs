-- | @boolean@ and related functions.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Language.PlutusCore.StdLib.Data.Bool
    ( bool
    , true
    , false
    , ifThenElse
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.Universe
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote

import           Language.PlutusCore.StdLib.Data.Unit

import           Language.PlutusCore.StdLib.Data.Function as Function
import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.Ck
import Language.PlutusCore

-- | 'Bool' as a PLC type.
bool :: uni `Includes` Bool => Type TyName uni ()
bool = mkTyBuiltin @Bool ()

-- | 'True' as a PLC term.
true :: (TermLike term TyName Name uni, uni `Includes` Bool) => term ()
true = mkConstant () True

-- | 'False' as a PLC term.
false :: (TermLike term TyName Name uni, uni `Includes` Bool) => term ()
false = mkConstant () False

-- | @if_then_else_@ as a PLC term.
--
-- > /\(A :: *) -> \(b : Bool) (x y : () -> A) -> ifThenElse {() -> A} b x y ()
ifThenElse :: (TermLike term TyName Name uni, uni `IncludesAll` '[Bool, ()], Rename (term ())) => term ()
ifThenElse = runQuote $ rename =<< do
    a <- freshTyName () "a"
    b <- freshName () "b"
    x <- freshName () "x"
    y <- freshName () "y"
    let unitFunA = TyFun () unit (TyVar () a)
    return
       . tyAbs () a (Type ())
      $ mkIterLamAbs [
          VarDecl () b bool,
          VarDecl () x unitFunA,
          VarDecl () y unitFunA
          ]
      $ mkIterApp ()
          (tyInst () (builtinNameAsTerm IfThenElse) unitFunA)
          [var () b, var () x, var () y, unitval]

-- >>> import PlutusPrelude
-- >>> putStrLn $ prettyString $ unNormalized $ fromRight undefined (runQuoteT (inferType defOffChainConfig ifThenElse) :: Either (TypeError DefaultUni ()) (Normalized (Type TyName DefaultUni ())))
-- (all a (type) (fun (con bool) (fun (fun (con unit) a) (fun (fun (con unit) a) a))))

appliedIfThenElse :: Term TyName Name DefaultUni ()
appliedIfThenElse =
    let int = mkTyBuiltin @Integer ()
        instConst = Apply () $ mkIterInst () Function.const [int, unit]
    in
            mkIterApp ()
                (TyInst () ifThenElse int)
                [mkConstant () True, instConst $ mkConstant @Integer () 0, instConst $ mkConstant @Integer () 1]

-- >>> import PlutusPrelude
-- >>> putStrLn $ prettyString $ unNormalized $ fromRight undefined (runQuoteT (inferType defOffChainConfig appliedIfThenElse) :: Either (TypeError DefaultUni ()) (Normalized (Type TyName DefaultUni ())))
-- <interactive>:107:103-119: error:
--     Variable not in scope:
--       appliedIfThenElse :: Term TyName Name DefaultUni ()
-- >>> putStrLn . prettyString $ unsafeEvaluateCek mempty appliedIfThenElse
-- <interactive>:108:28-44: error:
--     Variable not in scope: unsafeEvaluateCek :: t1 -> t0 -> a0
-- <interactive>:108:53-69: error:
--     Variable not in scope: appliedIfThenElse





-- ([],Apply () (Apply () (Apply () (Apply () (TyInst () (Builtin () (BuiltinName () IfThenElse)) (TyFun () (TyBuiltin () (Some (TypeIn unit))) (TyVar () (TyName {unTyName = Name {nameAttribute = (), nameString = "a", nameUnique = Unique {unUnique = 0}}})))) (Var () (Name {nameAttribute = (), nameString = "b", nameUnique = Unique {unUnique = 1}}))) (Var () (Name {nameAttribute = (), nameString = "x", nameUnique = Unique {unUnique = 2}}))) (Var () (Name {nameAttribute = (), nameString = "y", nameUnique = Unique {unUnique = 3}}))) (Constant () (Some (ValueOf unit ()))))
-- ([],Var () (Name {nameAttribute = (), nameString = "x", nameUnique = Unique {unUnique = 2}}))


-- >>> import PlutusPrelude
-- >>> import Language.PlutusCore.Pretty
-- >>> putStrLn $ docString $ prettyPlcReadableDebug appliedIfThenElse
-- ((/\(a_4 :: *) -> \(b_5 : bool) -> \(x_6 : unit -> a_4) -> \(y_7 : unit -> a_4) -> ifThenElse {unit -> a_4} b_5 x_6 y_7 ()) {integer} True ((/\(a_0 :: *) -> /\(b_1 :: *) -> \(x_2 : a_0) -> \(y_3 : b_1) -> x_2) {integer} {unit} 0) ((/\(a_0 :: *) -> /\(b_1 :: *) -> \(x_2 : a_0) -> \(y_3 : b_1) -> x_2) {integer} {unit} 1))

-- (/\(a_4 :: *) -> \(b_5 : bool) -> \(x_6 : unit -> a_4) -> \(y_7 : unit -> a_4) -> ifThenElse {unit -> a_4} b_5 x_6 y_7 ())
--   {integer}
--   True
--   ((/\(a_0 :: *) -> /\(b_1 :: *) -> \(x_2 : a_0) -> \(y_3 : b_1) -> x_2) {integer} {unit} 0)
--   ((/\(a_0 :: *) -> /\(b_1 :: *) -> \(x_2 : a_0) -> \(y_3 : b_1) -> x_2) {integer} {unit} 1)

-- (/\(a_4 :: *) -> \(b_5 : bool) -> \(x_6 : unit -> a_0) -> \(y_7 : unit -> a_4) -> x_6 ())
--   {integer}
--   True
--   ((/\(a_0 :: *) -> /\(b_1 :: *) -> \(x_2 : a_0) -> \(y_3 : b_1) -> x_2) {integer} {unit} 0)
--   ((/\(a_0 :: *) -> /\(b_1 :: *) -> \(x_2 : a_0) -> \(y_3 : b_1) -> x_2) {integer} {unit} 1)


-- > /\(A :: *) -> \(x : () -> A) -> x
force :: TermLike term TyName Name DefaultUni => term ()
force = runQuote $ do
    a <- freshTyName () "a"
    x <- freshName () "x"
    return
        . tyAbs () a (Type ())
        . lamAbs () x (TyFun () unit $ TyVar () a)
--         $ apply () (apply () (tyInst () idFun (TyFun () unit $ TyVar () a)) $ var () x) unitval
        $ apply () (var () x) unitval

-- > /\(A :: *) -> \(x : () -> A) -> x
force2 :: TermLike term TyName Name DefaultUni => term ()
force2 = runQuote $ do
    a <- freshTyName () "a"
    b <- freshName () "b"
    x <- freshName () "x"
    y <- freshName () "y"
    return
        . tyAbs () a (Type ())
        . lamAbs () b (mkTyBuiltin @Bool ())
        . lamAbs () x (TyFun () unit $ TyVar () a)
        . lamAbs () y (TyFun () unit $ TyVar () a)
--         $ apply () (apply () (tyInst () idFun (TyFun () unit $ TyVar () a)) $ var () y) unitval
        $ apply () (var () x) unitval

applied :: Term TyName Name DefaultUni ()
applied =
    let int = mkTyBuiltin @Integer ()
        instConst = Apply () $ mkIterInst () Function.const [int, unit]
    in
            mkIterApp ()
                (TyInst () force2 int)
                [mkConstant () True, instConst $ mkConstant @Integer () 0, instConst $ mkConstant @Integer () 1]

-- >>> import PlutusPrelude
-- >>> putStrLn $ prettyString $ unNormalized $ fromRight undefined (runQuoteT (inferType defOffChainConfig applied) :: Either (TypeError DefaultUni ()) (Normalized (Type TyName DefaultUni ())))
-- (con integer)
-- >>> putStrLn . prettyString $ unsafeEvaluateCek mempty applied
-- (Name {nameAttribute = ExMemory 118, nameString = "x", nameUnique = Unique {unUnique = 2}},LamAbs () (Name {nameAttribute = (), nameString = "y", nameUnique = Unique {unUnique = 3}}) (TyVar () (TyName {unTyName = Name {nameAttribute = (), nameString = "b", nameUnique = Unique {unUnique = 1}}})) (Var () (Name {nameAttribute = (), nameString = "x", nameUnique = Unique {unUnique = 2}})))
-- (Name {nameAttribute = ExMemory 118, nameString = "x", nameUnique = Unique {unUnique = 2}},Constant () (Some (ValueOf integer 0)))
-- (con 0)


-- [
--   [
--     [
--       {
--         (abs
--           a
--           (type)
--           (lam
--             b
--             (con bool)
--             (lam
--               x
--               (fun (con unit) a)
--               (lam
--                 y
--                 (fun (con unit) a)
--                 [
--                   [ [ [ { (builtin ifThenElse) (fun (con unit) a) } b ] x ] y ]
--                   (con ())
--                 ]
--               )
--             )
--           )
--         )
--         (con integer)
--       }
--       (con True)
--     ]
--     [
--       {
--         { (abs a (type) (abs b (type) (lam x a (lam y b x)))) (con integer) }
--         (con unit)
--       }
--       (con 0)
--     ]
--   ]
--   [
--     {
--       { (abs a (type) (abs b (type) (lam x a (lam y b x)))) (con integer) }
--       (con unit)
--     }
--     (con 1)
--   ]
-- ]





-- [
--   [
--     [
--       {
--         (abs
--           a
--           (type)
--           (lam
--             b
--             (con bool)
--             (lam x (fun (con unit) a) (lam y (fun (con unit) a) [ x (con ()) ]))
--           )
--         )
--         (con integer)
--       }
--       (con True)
--     ]
--     [
--       {
--         { (abs a (type) (abs b (type) (lam x a (lam y b x)))) (con integer) }
--         (con unit)
--       }
--       (con 0)
--     ]
--   ]
--   [
--     {
--       { (abs a (type) (abs b (type) (lam x a (lam y b x)))) (con integer) }
--       (con unit)
--     }
--     (con 1)
--   ]
-- ]



-- [ { (builtin ifThenElse) (fun (con unit) a) } b x y (con ()) ]



-- [Fun instIfThenElse, Arg const1] const0

-- computeCek [Fun instIfThenElse, Arg const1] (lam y b x), x :-> con 0

-- computeCek [Arg const1] (instIfThenElse (lam y b x)), x :-> con 0

-- computeCek [Fun (instIfThenElse (lam y b x)] const1, x :-> con 0

-- computeCek [] (instIfThenElse (lam y b x) (lam y b x))
