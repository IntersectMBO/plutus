module Infer(main) where

a = 'x'
f x = x
g x = [x,a]
h x = x + 1

xeven 0 = True
xeven n = xodd (n-1)
xodd 0 = False
xodd n = xeven (n-1)

main = do
  print a
  print (f (1::Int))
  print (f a)
  print (h (1::Int))
  print (even (2::Int))
