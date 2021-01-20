{-# LANGUAGE TemplateHaskell #-}
module Main where


import           Errors
import           Errors.TH.Bootstrap

main :: IO ()
main = do
    putStrLn "Printing TH-generated Haskell code:"
    putStrLn ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"
    $(bootstrap allErrors)
    putStrLn "\n<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<"
    putStrLn "Done printing."
