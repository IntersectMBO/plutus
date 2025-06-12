module OrPat where

data Sweet = Cupcake | Liquorice | Cookie | Raisins

taste :: Sweet -> Bool
tasty (Cupcake; Cookie) = True
tasty (Liquorice; Raisins) = False

main :: IO ()
main = print $ map tasty [Cupcake, Liquorice, Cupcake, Raisins]
