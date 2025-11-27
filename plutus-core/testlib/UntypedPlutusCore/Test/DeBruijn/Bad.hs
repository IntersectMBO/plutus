{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module UntypedPlutusCore.Test.DeBruijn.Bad
  ( var0
  , lamAbs1
  , fun0var0
  , fun1var0
  , fun1var1
  , deepFun1
  , deepOut0
  , deepMix0_1
  , deepMix1_0
  , deepOutMix1_0
  , manyFree01
  , iteStrict0
  , iteLazy0
  , ite10
  , illITEStrict
  , illITELazy
  , illPartialBuiltin
  , illAdd
  , illOverAppBuiltin
  , illOverAppFun
  ) where

import PlutusCore.Default
import PlutusCore.MkPlc
import PlutusCore.StdLib.Data.Bool
import PlutusCore.StdLib.Data.Unit
import PlutusPrelude
import UntypedPlutusCore
import UntypedPlutusCore.Test.DeBruijn.Good

-- | A definitely out-of-scope variable. Our variables start at index 1.
var0 :: Term DeBruijn uni fun ()
var0 = Var () $ DeBruijn 0

-- | Build a `LamAbs` with the binder having a non-sensical index.
lamAbs1 :: t ~ Term DeBruijn uni fun () => t -> t
lamAbs1 = LamAbs () $ DeBruijn 1

fun0var0, fun1var0, fun1var1 :: Term DeBruijn DefaultUni DefaultFun ()
fun0var0 = lamAbs0 var0
fun1var0 = lamAbs1 var0
fun1var1 = lamAbs1 $ Var () $ DeBruijn 1

{-| (lam1 ...n.... (Var n))
Wrong binders, Well-scoped variable -}
deepFun1 :: Natural -> Term DeBruijn DefaultUni DefaultFun ()
deepFun1 n =
  timesA n lamAbs1 $
    Var () $
      DeBruijn $
        fromIntegral n

{-| (lam0 ...n.... (Var n+1))
Correct binders, Out-of-scope variable -}
deepOut0 :: Natural -> Term DeBruijn DefaultUni DefaultFun ()
deepOut0 n =
  timesA n lamAbs0 $
    Var () $
      DeBruijn $
        fromIntegral $
          n + 1

{-| (lam0 ...n.... lam1 ...n.... (Var n+n))
Mix of correct and wrong binders, Well-scoped variable -}
deepMix0_1 :: Natural -> Term DeBruijn DefaultUni DefaultFun ()
deepMix0_1 n =
  timesA n lamAbs0 $
    timesA n lamAbs1 $
      Var () $
        DeBruijn $
          fromIntegral $
            n + n

{-| (lam1 ...n.... lam0 ...n.... (Var n+n))
Mix of wrong and correct binders, well-scoped variable -}
deepMix1_0 :: Natural -> Term DeBruijn DefaultUni DefaultFun ()
deepMix1_0 n =
  timesA n lamAbs1 $
    timesA n lamAbs0 $
      Var () $
        DeBruijn $
          fromIntegral $
            n + n

{-| (lam1 ...n.... lam0 ...n.... (Var n+n+1))
Mix of correct and wrong binders, out-of-scope variable -}
deepOutMix1_0 :: Natural -> Term DeBruijn DefaultUni DefaultFun ()
deepOutMix1_0 n =
  timesA n lamAbs1 $
    timesA n lamAbs0 $
      Var () $
        DeBruijn $
          fromIntegral $
            n + n + 1

{-| [(force (builtin ifThenElse) (con bool True) (con bool True) var99]
Both branches are evaluated *before* the predicate,
so it is clear that this should fail in every case. -}
iteStrict0 :: Term DeBruijn DefaultUni DefaultFun ()
iteStrict0 =
  Force () (Builtin () IfThenElse)
    @@ [ true -- pred
       , true -- then
       , var0 -- else
       ]

{-| [(force (builtin ifThenElse) (con bool True) (delay true) (delay var99)]
The branches are *lazy*. The evaluation result (success or failure) depends on how the machine
ignores  the irrelevant to the computation) part of the environment. -}
iteLazy0 :: Term DeBruijn DefaultUni DefaultFun ()
iteLazy0 =
  Force () (Builtin () IfThenElse)
    @@ [ true -- pred
       , Delay () true -- then
       , Delay () var0 -- else
       ]

-- | [(force (builtin ifThenElse) (con bool True) (lam0 var1) (lam1 var0)]
ite10 :: Term DeBruijn DefaultUni DefaultFun ()
ite10 =
  Force () (Builtin () IfThenElse)
    @@ [ true -- pred
       , idFun0 -- then
       , fun1var0 -- else
       ]

-- | An example with a lot of free vars
manyFree01 :: Term DeBruijn DefaultUni DefaultFun ()
manyFree01 =
  timesA 5 (Apply () (timesA 10 forceDelay var0)) $
    timesA 20 forceDelay $
      Var () $
        DeBruijn 1
  where
    forceDelay = Force () . Delay ()

-- * Examples will ill-typed terms

{-| [(force (builtin ifThenElse) (con bool True) (con bool  True) (con unit ())]
Note that the branches have **different** types. The machine cannot catch such a type error. -}
illITEStrict :: Term DeBruijn DefaultUni DefaultFun ()
illITEStrict =
  Force () (Builtin () IfThenElse)
    @@ [ true -- pred
       , true -- then
       , unitval -- else
       ]

{-| [(force (builtin ifThenElse) (con bool True) (lam x (con bool  True)) (lam x (con unit ()))]
The branches are *lazy*. Note that the branches have **different** types.
The machine cannot catch such a type error. -}
illITELazy :: Term DeBruijn DefaultUni DefaultFun ()
illITELazy =
  Force () (Builtin () IfThenElse)
    @@ [ true -- pred
       , lamAbs0 true -- then
       , Delay () true -- else
       ]

{-| [(builtin addInteger) (con integer 1) (con unit ())]
Interesting because it involves a runtime type-error of a builtin. -}
illAdd :: Term DeBruijn DefaultUni DefaultFun ()
illAdd =
  Builtin () AddInteger
    @@ [ one
       , unitval
       ]

{-| [(builtin addInteger) (con integer 1) (con integer 1) (con integer 1)]
Interesting because it involves a (builtin) over-saturation type-error,
which the machine can recognize. -}
illOverAppBuiltin :: Term DeBruijn DefaultUni DefaultFun ()
illOverAppBuiltin =
  Builtin () AddInteger
    @@ [ one
       , one
       , one
       ]

{-| [(lam x x) (con integer 1) (con integer 1)]
Interesting because it involves a (lambda) over-saturation type-error,
which the machine can recognize. -}
illOverAppFun :: Term DeBruijn DefaultUni DefaultFun ()
illOverAppFun =
  idFun0
    @@ [ one
       , one
       ]

{-| [addInteger true]
this relates to the immediate vs deferred unlifting.
this used to be an immediate type error but now it is deferred until saturation. -}
illPartialBuiltin :: Term DeBruijn DefaultUni DefaultFun ()
illPartialBuiltin = Apply () (Builtin () AddInteger) true

-- helpers

one :: Term name DefaultUni fun ()
one = mkConstant @Integer () 1
