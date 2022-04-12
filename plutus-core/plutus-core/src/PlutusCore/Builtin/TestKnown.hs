{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE QuantifiedConstraints   #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | A module providing a tool for making sure that each type from a particular universe implements
-- 'KnownTypeAst', 'ReadKnown' and 'MakeKnown'. Kept separate from the modules defining those
-- classes in order not to introduce dependencies between them and because this extra safety is
-- scary looking and it's best to keep it separate from what is necessary.
module PlutusCore.Builtin.TestKnown
    ( TestTypesFromTheUniverseAreAllKnown
    ) where

import PlutusCore.Builtin.KnownType
import PlutusCore.Builtin.KnownTypeAst

import Universe

-- | For providing a 'KnownTypeAst' instance for a built-in type it's enough for that type to satisfy
-- 'KnownBuiltinTypeAst'.
class    (KnownBuiltinTypeAst uni a => KnownTypeAst uni a) => ImplementedKnownTypeAst uni a
instance (KnownBuiltinTypeAst uni a => KnownTypeAst uni a) => ImplementedKnownTypeAst uni a

-- | For providing a 'ReadKnownIn' instance for a built-in type it's enough for that type to be in
-- the universe.
class    (uni `Contains` a => ReadKnownIn uni a) => ImplementedReadKnownIn uni a
instance (uni `Contains` a => ReadKnownIn uni a) => ImplementedReadKnownIn uni a

-- | For providing a 'MakeKnownIn' instance for a built-in type it's enough for that type to be in
-- the univese.
class    (uni `Contains` a => MakeKnownIn uni a) => ImplementedMakeKnownIn uni a
instance (uni `Contains` a => MakeKnownIn uni a) => ImplementedMakeKnownIn uni a

-- | An instance of this class not having any constraints ensures that every type (according to
-- 'Everywhere') from the universe has 'KnownTypeAst, 'ReadKnownIn' and 'MakeKnownIn' instances.
class
    ( uni `Everywhere` ImplementedKnownTypeAst uni
    , uni `Everywhere` ImplementedReadKnownIn uni
    , uni `Everywhere` ImplementedMakeKnownIn uni
    ) => TestTypesFromTheUniverseAreAllKnown uni
