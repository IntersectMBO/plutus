data WoC = WoC
type instance HasPrettyDefaults WoC = 'False
instance NonDefaultPrettyBy WoC Char
instance NonDefaultPrettyBy WoC Strict.Text
instance NonDefaultPrettyBy WoC Integer where
    nonDefaultPrettyBy _ _ = pretty "0"
instance (PrettyBy WoC a, PrettyBy WoC b) => NonDefaultPrettyBy WoC (a, b)
instance PrettyBy WoC a => NonDefaultPrettyBy WoC (Maybe a) where
    nonDefaultPrettyBy _ Nothing  = pretty "Nothing"
    nonDefaultPrettyBy _ (Just x) = pretty "Just" <+> parens (prettyBy WoC x)

    nonDefaultPrettyListBy = defaultPrettyFunctorBy
instance PrettyBy WoC a => NonDefaultPrettyBy WoC [a]
--     nonDefaultPrettyBy = defaultPrettyFunctorBy

instance PrettyBy WoC WoC where
    prettyBy _ _ = pretty "WoC"

-- >>> prettyBy WoC (1 :: Integer)
-- 0
-- >>> prettyBy WoC (1 :: Integer, 2 :: Integer)
-- (0, 0)
-- >>> prettyBy WoC [Just 'a', Nothing, Just 'b']
-- [Just (a), Nothing, Just (b)]
-- >>> prettyBy WoC "abc"
-- abc
-- >>> prettyBy WoC (1 :: Integer, WoC)
-- (0, WoC)
