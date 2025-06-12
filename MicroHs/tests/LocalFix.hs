module LocalFix where

main :: IO ()
main = do
  let
    (.-) :: Int -> Int -> Int
    (.-) = (-)
    x = 1 .- 2 .- 3
  print x
  let
    infixr .-
    (.-) :: Int -> Int -> Int
    (.-) = (-)
    x = 1 .- 2 .- 3
  print x
