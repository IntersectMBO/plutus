import Examples

main :: IO ()
main = do

  -- deterministic tests. comment out after first run.
  testFixed veryDense [1..10] "worst-case.dat"
  testFixed thinCycle [1..20] "small-nontrivial.dat"
  testFixed diagonal  [1..20] "trivial.dat"


  -- randomized tests.
  let range = [1..9] -- we test systems of 1..9 types at each density.
      times = 100    -- each size/density pairing is run 100 times.
      test :: Probability -> IO ()
      test density = testRandom range times density ("density " ++ (show density) ++ ".dat")

  mapM_ test [10,20,30,40,50,60,70,80,90]






