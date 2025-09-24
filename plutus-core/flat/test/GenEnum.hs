-- generate test enumerations
g =
    let n = 256
    in  unwords
            [ "data E" ++ show n
            , "="
            , intercalate " | " $ map (("N" ++) . show) [1 .. n]
            , "deriving (Show,Generic,Flat)"
            ]


