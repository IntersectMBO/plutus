{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
{-# OPTIONS_GHC -fno-warn-simplifiable-class-constraints #-}

{-# LANGUAGE DataKinds #-}

-- | This module helps to visualize and debug the 'TypeScheme' inference machinery from the
-- @Meaning@ module.
module PlutusCore.Builtin.Debug
  ( elaborateDebug
  -- Reexporting a bunch of stuff, so that debug output is not littered with module names.
  , module Export
  ) where

import PlutusCore.Builtin.Elaborate as Export
import PlutusCore.Builtin.Polymorphism as Export
import PlutusCore.Core as Export
import PlutusCore.Default as Export
import PlutusCore.Name as Export

-- | Instantiate type variables in the type of a value using 'ElaborateFromTo'. Example usages:
--
-- >>> :t elaborateDebug False
-- elaborateDebug False :: Bool
-- >>> :t elaborateDebug $ \_ -> ()
-- elaborateDebug $ \_ -> ()
--   :: Opaque
--        (Term TyName Name DefaultUni DefaultFun ())
--        (TyVarRep ('TyNameRep "a" 0))
--      -> ()
-- >>> :t elaborateDebug $ Just ()
-- <interactive>:1:1: error:
--     • No instance for ‘KnownTypeAst DefaultUni (Maybe ())’
--       Which means
--         ‘Maybe ()’
--       is neither a built-in type, nor one of the control types.
--       If it can be represented in terms of one of the built-in types
--         then go add the instance (you may need a ‘KnownTypeIn’ one too)
--         alongside the instance for the built-in type.
--       Otherwise you may need to add a new built-in type
--         (provided you're doing something that can be supported in principle)
--     • In the expression: elaborateDebug $ Just ()
-- >>> :t elaborateDebug $ 0 + 42
-- <interactive>:1:18: error:
--     • Built-in functions are not allowed to have constraints
--       To fix this error instantiate all constrained type variables
--     • In the second argument of ‘($)’, namely ‘0 + 42’
--       In the expression: elaborateDebug $ 0 + 42
elaborateDebug
    :: forall a j. ElaborateFromTo 0 j (Term TyName Name DefaultUni DefaultFun ()) a
    => a -> a
elaborateDebug = id
