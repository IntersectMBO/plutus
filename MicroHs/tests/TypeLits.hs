module TypeLits(main) where
import Data.TypeLits

data PS (s :: Symbol) = PS
data PN (s :: Nat) = PN

natValInt :: forall (n :: Nat) . KnownNat n => PN n -> Int
natValInt p = fromInteger (natVal p)

main :: IO ()
main = do
  print $ symbolVal (PS :: PS "hello")
  print $ natVal (PN :: PN 42)
  print $ natValInt (PN :: PN 42)
