module Test.Data2.Flat(module Test.Data2) where
import Flat
import Test.Data2

instance Flat a => Flat (List a)
