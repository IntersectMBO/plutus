module NoForall where

-- Without an explicit forall the 'a' is not bound in the body.
f :: a -> ((a,a),(a,a))
f x =
  let g :: a -> (a,a)
      g a = (a,a)
  in  g (x,x)

main :: IO ()
main = print (f True)
