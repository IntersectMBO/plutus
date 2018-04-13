Test data concerning size increase of datatypes when removing mutual recursion from the system via the Bekic identity can be found in results/test-results.md

You can also run your own tests:

How to use:

1. Install 'stack' (https://docs.haskellstack.org/en/stable/README/)

2. In the directory where the repository lives, run
   > stack build

Now, to run the same tests used to generate the data summarized in test-results.md:
   > stack exec fomega-exe

You can also play with the system. I suggest enabling quasiquotes in GHCI:
   > stack ghci --ghci-options -XQuasiQuotes src/Examples.hs

You can now get the mutual recursion and algebraic types out of signatures with
   > ghci> runExample example

Some examples to try are "fgh","treeforest","onlyList", "multi", and "(generate (veryDense 3))". See also the function "generate" in Examples.hs.
You can parse declarations of algebraic types using the quasiquoter, as in
  > ghci> list_decl = algDecl [declExp| all. 1 + ((list a) * a)  |]

If you are only interested in the size of an example before and after mutual recursion and algebraic types have been removed, try
  > ghci> onlySizes example
