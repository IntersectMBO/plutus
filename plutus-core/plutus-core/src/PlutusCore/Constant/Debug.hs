{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module helps to visualize and debug the 'TypeScheme' inference machinery from the
-- @Meaning@ module.
module PlutusCore.Constant.Debug where

import PlutusCore.Constant.Meaning
import PlutusCore.Constant.Typed
import PlutusCore.Core
import PlutusCore.Default
import PlutusCore.Name

type TermDebug = Term TyName Name DefaultUni DefaultFun ()

-- | Instantiate type variables in the type of a value using 'EnumerateFromTo'.
-- This function only performs the enumeration and checks that the result does not have certain
-- constraints, so it's allowed for the type to reference types that are not in the universe.
-- Example usages:
--
-- >>> :t enumerateDebug False
-- enumerateDebug False :: Bool
-- >>> :t enumerateDebug $ Just 'a'
-- enumerateDebug $ Just 'a' :: Maybe Char
-- >>> :t enumerateDebug $ \_ -> ()
-- enumerateDebug $ \_ -> ()
--   :: Opaque
--        (Term TyName Name DefaultUni DefaultFun ())
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

-- | Instantiate type variables in the type of a value using 'EnumerateFromTo' and check that it's
-- possible to construct a 'TypeScheme' out of the resulting type. Example usages:
--
-- >>> :t inferDebug False
-- inferDebug False :: Bool
-- >>> :t inferDebug $ Just 'a'
-- <interactive>:1:1-21: error:
--     • There's no 'KnownType' instance for Maybe Char
--       Did you add a new built-in type and forget to provide a 'KnownType' instance for it?
--     • In the expression: inferDebug $ Just 'a'
-- >>> :t inferDebug $ \_ -> ()
-- inferDebug $ \_ -> ()
--   :: Opaque
--        (Term TyName Name DefaultUni DefaultFun ())
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
