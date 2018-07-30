-- parseScoped :: BSL.ByteString -> Either ParseError (Program TyName Name AlexPosn)
-- parseScoped = fmap (uncurry rename) . parseST

-- data Program tyname name a = Program a (Version a) (Term tyname name a)
--                  deriving (Show, Eq, Functor, Generic, NFData)
