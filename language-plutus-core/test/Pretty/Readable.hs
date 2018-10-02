module Pretty.Readable (test_PrettyReadable) where

import           Language.PlutusCore
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.ChurchNat
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Data.Unit

import           Common

import           Test.Tasty

testReadable :: PrettyPlc a => TestName -> a -> TestNestedGolden
testReadable name
    = nestedGoldenVsDoc name
    . prettyPlcReadableBy (botPrettyConfigReadable defPrettyConfigName)

test_PrettyReadable :: TestTree
test_PrettyReadable =
    runTestNestedGoldenIn "test/Pretty/Golden/Readable" $
        testNestedGolden "StdLib"
            [ testNestedGolden "Bool"
                  [ testReadable "Bool"  $ runQuote getBuiltinBool
                  , testReadable "True"  $ runQuote getBuiltinTrue
                  , testReadable "False" $ runQuote getBuiltinFalse
                  , testReadable "If"    $ runQuote getBuiltinIf
                  ]
            , testNestedGolden "ChurchNat"
                  [ testReadable "ChurchNat"  $ runQuote getBuiltinChurchNat
                  , testReadable "ChurchZero" $ runQuote getBuiltinChurchZero
                  , testReadable "ChurchSucc" $ runQuote getBuiltinChurchSucc
                  ]
            , testNestedGolden "Function"
                  [ testReadable "Const"  $ runQuote getBuiltinConst
                  -- , testReadable "Self"   $ runQuote getBuiltinSelf
                  , testReadable "Unroll" $ runQuote getBuiltinUnroll
                  , testReadable "Fix"    $ runQuote getBuiltinFix
                  ]
            , testNestedGolden "List"
                  [ -- testReadable "List"      $ runQuote getBuiltinList
                    testReadable "Nil"       $ runQuote getBuiltinNil
                  , testReadable "Cons"      $ runQuote getBuiltinCons
                  , testReadable "FoldrList" $ runQuote getBuiltinFoldrList
                  , testReadable "FoldList"  $ runQuote getBuiltinFoldList
                  ]
            , testNestedGolden "Nat"
                  [ -- testReadable "Nat"      $ runQuote getBuiltinNat
                    testReadable "Zero"     $ runQuote getBuiltinZero
                  , testReadable "Succ"     $ runQuote getBuiltinSucc
                  , testReadable "FoldrNat" $ runQuote getBuiltinFoldrNat
                  , testReadable "FoldNat"  $ runQuote getBuiltinFoldNat
                  ]
            , testNestedGolden "Unit"
                  [ testReadable "Unit"    $ runQuote getBuiltinUnit
                  , testReadable "Unitval" $ runQuote getBuiltinUnitval
                  ]
            ]
