{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
{-# OPTIONS_GHC -fno-warn-simplifiable-class-constraints #-}

{-| This module helps to visualize and debug the 'BuiltinMeaning' inference machinery from the
@Elaborate@ and @Meaning@ modules. -}
module PlutusCore.Builtin.Debug
  ( elaborateDebug
  , makeBuiltinMeaningDebug
  -- Reexporting a bunch of stuff, so that debug output is not littered with module names.
  , module Export
  ) where

import PlutusCore.Builtin.Elaborate as Export
import PlutusCore.Builtin.Meaning as Export
import PlutusCore.Builtin.Polymorphism as Export
import PlutusCore.Core as Export
import PlutusCore.Default as Export
import PlutusCore.Name.Unique as Export

{-| Instantiate type variables in the type of a value using 'ElaborateFromTo'. Example usages:

>>> :t elaborateDebug False
elaborateDebug False :: Bool
>>> :t elaborateDebug fst
elaborateDebug fst
  :: (TyVarRep ('TyNameRep "a" 0), TyVarRep ('TyNameRep "b" 1))
     -> TyVarRep ('TyNameRep "a" 0) -}
elaborateDebug
  :: forall a j
   . ElaborateFromTo DefaultUni 0 j (Term TyName Name DefaultUni DefaultFun ()) a
  => a -> a
elaborateDebug = id

-- >>> :t makeBuiltinMeaningDebug $ \_ -> ()
-- makeBuiltinMeaningDebug $ \_ -> ()
--   :: Opaque
--        (Term TyName Name DefaultUni DefaultFun ())
--        (TyVarRep ('TyNameRep "a" 0))
--      -> ()
-- >>> :t makeBuiltinMeaningDebug False
-- <interactive>:1:1: error: [GHC-64725]
--     • A built-in function must take at least one type or term argument
--       ‘Bool’ is a built-in type so you can embed any of its values as a constant
--       If you still want a built-in function, add a dummy ‘()’ argument
--     • In the expression: makeBuiltinMeaningDebug False
-- >>> :t makeBuiltinMeaningDebug $ 0 + 42
-- <interactive>:1:29: error: [GHC-64725]
--     • Built-in functions are not allowed to have constraints
--       To fix this error instantiate all constrained type variables
--     • In the second argument of ‘($)’, namely ‘0 + 42’
--       In the expression: makeBuiltinMeaningDebug $ 0 + 42
-- >>> :t makeBuiltinMeaningDebug $ Just ()
-- <interactive>:1:1: error: [GHC-64725]
--     • No instance for ‘KnownTypeAst DefaultUni (Maybe ())’
--       Which means
--         ‘Maybe ()’
--       is neither a built-in type, nor one of the control types.
--       If it can be represented in terms of one of the built-in types
--         then go add the instance (you may need a few others too)
--         alongside the instance for the built-in type.
--       Otherwise you may need to add a new built-in type
--         (provided you're doing something that can be supported in principle)
--     • In the first argument of ‘($)’, namely ‘makeBuiltinMeaningDebug’
--       In the expression: makeBuiltinMeaningDebug $ Just ()
-- >>> :t makeBuiltinMeaningDebug fst
-- <interactive>:1:1: error: [GHC-64725]
--     • An unwrapped built-in type constructor can't be applied to a type variable
--       Are you trying to define a polymorphic built-in function over a polymorphic type?
--       In that case you need to wrap all polymorphic built-in types applied to type
--        variables with either ‘SomeConstant’ or ‘Opaque’ depending on whether its the
--        type of an argument or the type of the result, respectively
--     • In the expression: makeBuiltinMeaningDebug fst
-- >>> :t makeBuiltinMeaningDebug null
-- <interactive>:1:1: error: [GHC-64725]
--     • No instance for ‘KnownTypeAst DefaultUni (TyVarRep
--                                                   ('TyNameRep "f" 0) a)’
--       Which means
--         ‘TyVarRep ('TyNameRep "f" 0) a’
--       is neither a built-in type, nor one of the control types.
--       If it can be represented in terms of one of the built-in types
--         then go add the instance (you may need a few others too)
--         alongside the instance for the built-in type.
--       Otherwise you may need to add a new built-in type
--         (provided you're doing something that can be supported in principle)
--     • In the expression: makeBuiltinMeaningDebug null
-- <interactive>:1:1: error: [GHC-64725]
--     • A built-in function is not allowed to have applied type variables in its type
--       To fix this error specialize all higher-kinded type variables
--     • In the expression: makeBuiltinMeaningDebug null
-- >>> :t makeBuiltinMeaningDebug (undefined :: Opaque val (f Bool) -> ())
-- <interactive>:1:1: error: [GHC-64725]
--     • No instance for ‘KnownTypeAst DefaultUni (TyVarRep
--                                                   ('TyNameRep "f" 0) Bool)’
--       Which means
--         ‘TyVarRep ('TyNameRep "f" 0) Bool’
--       is neither a built-in type, nor one of the control types.
--       If it can be represented in terms of one of the built-in types
--         then go add the instance (you may need a few others too)
--         alongside the instance for the built-in type.
--       Otherwise you may need to add a new built-in type
--         (provided you're doing something that can be supported in principle)
--     • In the expression:
--         makeBuiltinMeaningDebug (undefined :: Opaque val (f Bool) -> ())
-- <interactive>:1:1: error: [GHC-64725]
--     • A built-in function is not allowed to have applied type variables in its type
--       To fix this error apply type variables via explicit ‘TyAppRep’
--     • In the expression:
--         makeBuiltinMeaningDebug (undefined :: Opaque val (f Bool) -> ())
makeBuiltinMeaningDebug
  :: forall a
   . MakeBuiltinMeaning a (Term TyName Name DefaultUni DefaultFun ())
  => a -> a
makeBuiltinMeaningDebug = id
