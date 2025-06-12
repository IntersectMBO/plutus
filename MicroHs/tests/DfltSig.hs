module DfltSig where

class Def a where
  def :: a
  default def :: Enum a => a
  def = toEnum 0

instance Def Int
instance Def Char
instance Def [a] where def = []

main :: IO ()
main = print (def::Int, def::Char,def::[Bool])
