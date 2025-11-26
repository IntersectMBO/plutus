{-| Some basic Template Haskell to reduce boilerplate in the cost model tests.
   We have to put this in a separate source file because of staging
   restrictions. -}
module TH (genTest) where

import Data.Char (toUpper)
import Language.Haskell.TH

toUpper1 :: String -> String
toUpper1 [] = error "empty string in toUpper1"
toUpper1 (c : cs) = toUpper c : cs

mkIterApp :: Exp -> [Exp] -> Exp
mkIterApp = foldl AppE

{-| The genTest function generates calls to the appropriate "makeProp" functions: eg

      $(genTest 3 "xyz") -> makeProp3 "xyz" paramXyz modelsH modelsR

   Appropriate variables/functions must be in scope when 'genTest' is called,
   but this should always be the case if it's used inside the 'tests' list in
   TestCostModels (and the error messages are very helpful if something goes
   wrong). Note that we can supply extra arguments after the generated code if
   makePropN requires them: we use this when generating tests for makeProp2. -}
genTest :: Int -> String -> Q Exp
genTest n s =
  let makePropN = VarE $ mkName ("makeProp" ++ show n)
      testname = LitE $ StringL s
      params = VarE $ mkName ("param" ++ toUpper1 s)
      modelsH = VarE $ mkName "modelsH"
      modelsR = VarE $ mkName "modelsR"
   in pure $ mkIterApp makePropN [testname, params, modelsH, modelsR]
