# Marlowe HSpec

This package contains a ready-made HSpec `Expectation` to check that Marlowe Contracts cannot produce warnings at runtime.

This uses the SBV library to effectively run many execution paths so depending on your contract it could take a lot of time and space.

## Basic Use

```haskell
main :: IO ()
main = hspec $ do
    describe "My Contract" $
        it "should not produce any warnings at runtime" $ assertNoWarnings myContract
    where
        myContract = Close
```