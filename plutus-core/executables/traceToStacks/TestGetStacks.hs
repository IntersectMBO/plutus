import Common
import Data.Text (Text, singleton)
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

toText :: Char -> Text
toText = singleton

xEvent :: [ProfileEvent]
xEvent = [
    MkProfileEvent 0 Enter (toText 'x'),
    MkProfileEvent 1 Exit (toText 'x')
    ]

xStackVal :: [StackVal]
xStackVal = [MkStackVal [toText 'x'] 1]

zInyInxEvent :: [ProfileEvent]
zInyInxEvent = [
    MkProfileEvent 0 Enter (toText 'x'),
    MkProfileEvent 1 Enter (toText 'y'),
    MkProfileEvent 10 Enter (toText 'z'),
    MkProfileEvent 100 Exit (toText 'z'),
    MkProfileEvent 1000 Exit (toText 'y'),
    MkProfileEvent 10000 Exit (toText 'x')
    ]

zInyInxStackVals :: [StackVal]
zInyInxStackVals = [
    MkStackVal [toText 'z', toText 'y', toText 'x'] 90,
    MkStackVal [toText 'y', toText 'x'] 909,
    MkStackVal [toText 'x'] 9001
    ]

yzInxEvent :: [ProfileEvent]
yzInxEvent = [
    MkProfileEvent 0 Enter (toText 'x'),
    MkProfileEvent 1 Enter (toText 'y'),
    MkProfileEvent 10 Exit (toText 'y'),
    MkProfileEvent 100 Enter (toText 'z'),
    MkProfileEvent 1000 Exit (toText 'z'),
    MkProfileEvent 10000 Exit (toText 'x')
    ]

yzInxStackVals :: [StackVal]
yzInxStackVals = [
    MkStackVal [toText 'y', toText 'x'] 9,
    MkStackVal [toText 'z', toText 'x'] 900,
    MkStackVal [toText 'x'] 9091
    ]

kInyzInxEvent :: [ProfileEvent]
kInyzInxEvent = [
    MkProfileEvent 0 Enter (toText 'x'),
    MkProfileEvent 1 Enter (toText 'y'),
    MkProfileEvent 10 Enter (toText 'k'),
    MkProfileEvent 100 Exit (toText 'k'),
    MkProfileEvent 1000 Exit (toText 'y'),
    MkProfileEvent 10000 Enter (toText 'z'),
    MkProfileEvent 100000 Exit (toText 'z'),
    MkProfileEvent 1000000 Exit (toText 'x')
    ]

kInyzInxStackVals :: [StackVal]
kInyzInxStackVals = [
    MkStackVal [toText 'k', toText 'y', toText 'x'] 90,
    MkStackVal [toText 'y', toText 'x'] 909,
    MkStackVal [toText 'z', toText 'x'] 90000,
    MkStackVal [toText 'x'] 909001
    ]

main :: IO ()
main = defaultMain $ testGroup "getStacks tests" [
    testCase "x only" (getStacks xEvent @?= xStackVal),
    testCase "x calls y calling z" (getStacks zInyInxEvent @?= zInyInxStackVals),
    testCase "x calls y and z" (getStacks yzInxEvent @?= yzInxStackVals),
    testCase "x calls y and z with y calling k" (getStacks kInyzInxEvent @?= kInyzInxStackVals)
    ]
