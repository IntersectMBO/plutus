{-# LANGUAGE EmptyDataDecls #-}

-- | The @DerivingVia@ sentinel type recognised by the Plinth deriving plugin.
module PlutusTx.Plugin.Deriving.Via (Plinth) where

{-| Used as a @DerivingVia@ target to activate the deriving plugin, e.g.

> data Foo = Foo Integer Integer
>   deriving AsData via Plinth

When the plugin is active the deriving clause is rewritten away at parse
time, so @Plinth@ never actually has to be in scope. Defining it as a real
type means that when the plugin is /not/ loaded GHC reports a clean error
instead of a confusing one. -}
data Plinth
