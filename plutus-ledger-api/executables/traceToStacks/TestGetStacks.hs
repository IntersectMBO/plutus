{-# LANGUAGE OverloadedStrings #-}

import Common
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

-- | A list of @ProfileEvent@ simulating a function @x@ using 1 resource.
xEvent :: [ProfileEvent]
xEvent =
  [ MkProfileEvent 0 Enter "x"
  , MkProfileEvent 1 Exit "x"
  ]

-- | The list of @StackVal@ that corresponds to @xEvent@.
xStackVal :: [StackVal]
xStackVal = [MkStackVal ["x"] 1]

-- | A list of @ProfileEvent@ simulating function @x@ calling @y@ calling @z@.
zInyInxEvent :: [ProfileEvent]
zInyInxEvent =
  [ MkProfileEvent 0 Enter "x"
  , MkProfileEvent 1 Enter "y"
  , MkProfileEvent 10 Enter "z"
  , MkProfileEvent 100 Exit "z"
  , MkProfileEvent 1000 Exit "y"
  , MkProfileEvent 10000 Exit "x"
  ]

-- | The list of @StackVal@ that corresponds to @zInyInxEvent@.
zInyInxStackVals :: [StackVal]
zInyInxStackVals =
  [ MkStackVal ["z", "y", "x"] 90
  , MkStackVal ["y", "x"] 909
  , MkStackVal ["x"] 9001
  ]

-- | A list of @ProfileEvent@ simulating function @x@ calling @y@ and @z@.
yzInxEvent :: [ProfileEvent]
yzInxEvent =
  [ MkProfileEvent 0 Enter "x"
  , MkProfileEvent 1 Enter "y"
  , MkProfileEvent 10 Exit "y"
  , MkProfileEvent 100 Enter "z"
  , MkProfileEvent 1000 Exit "z"
  , MkProfileEvent 10000 Exit "x"
  ]

-- | The list of @StackVal@ that corresponds to @yzInxEvent@.
yzInxStackVals :: [StackVal]
yzInxStackVals =
  [ MkStackVal ["y", "x"] 9
  , MkStackVal ["z", "x"] 900
  , MkStackVal ["x"] 9091
  ]

-- | A list of @ProfileEvent@ simulating a function @x@ calling @y@ and @z@, with @y@ calling @k@.
kInyzInxEvent :: [ProfileEvent]
kInyzInxEvent =
  [ MkProfileEvent 0 Enter "x"
  , MkProfileEvent 1 Enter "y"
  , MkProfileEvent 10 Enter "k"
  , MkProfileEvent 100 Exit "k"
  , MkProfileEvent 1000 Exit "y"
  , MkProfileEvent 10000 Enter "z"
  , MkProfileEvent 100000 Exit "z"
  , MkProfileEvent 1000000 Exit "x"
  ]

-- | The list of @StackVal@ that corresponds to @kInyzInxEvent@.
kInyzInxStackVals :: [StackVal]
kInyzInxStackVals =
  [ MkStackVal ["k", "y", "x"] 90
  , MkStackVal ["y", "x"] 909
  , MkStackVal ["z", "x"] 90000
  , MkStackVal ["x"] 909001
  ]

main :: IO ()
main =
  defaultMain $
    testGroup
      "getStacks tests"
      [ testCase "x only" (getStacks xEvent @?= xStackVal)
      , testCase "x calls y calling z" (getStacks zInyInxEvent @?= zInyInxStackVals)
      , testCase "x calls y and z" (getStacks yzInxEvent @?= yzInxStackVals)
      , testCase "x calls y and z with y calling k" (getStacks kInyzInxEvent @?= kInyzInxStackVals)
      ]
