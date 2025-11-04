{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
-- CSE is very unstable and produces different output, likely depending on the version of either
-- @unordered-containers@ or @hashable@.
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module AssocMap.Golden where

import PlutusTx.Code
import PlutusTx.Data.AssocMap qualified as Data.AssocMap
import PlutusTx.IsData ()
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.TH (compile)
import PlutusTx.These (these)

-- | Test the performance and interaction between 'insert', 'delete' and 'lookup'.
map1
  :: CompiledCode
       ( Integer
         -> ( Maybe Integer
            , Maybe Integer
            , Maybe Integer
            , Maybe Integer
            , Maybe Integer
            )
       )
map1 =
  $$( compile
        [||
        \n ->
          let m :: Data.AssocMap.Map Integer Integer
              m =
                foldr
                  (\i -> Data.AssocMap.insert (n PlutusTx.+ i) i)
                  (Data.AssocMap.singleton n 0)
                  (PlutusTx.enumFromTo 1 10)
              m' = Data.AssocMap.delete (n PlutusTx.+ 5) m
           in ( Data.AssocMap.lookup n m
              , Data.AssocMap.lookup (n PlutusTx.+ 5) m
              , Data.AssocMap.lookup (n PlutusTx.+ 10) m
              , Data.AssocMap.lookup (n PlutusTx.+ 20) m
              , Data.AssocMap.lookup (n PlutusTx.+ 5) m'
              )
        ||]
    )

{-| Test that 'unionWith' is implemented correctly. Due to the nature of 'Map k v',
some type errors are only caught when running the PlutusTx compiler on code which uses
'unionWith'.
-}
map2 :: CompiledCode (Integer -> [(Integer, Integer)])
map2 =
  $$( compile
        [||
        \n ->
          let m1 :: Data.AssocMap.Map Integer Integer
              m1 =
                Data.AssocMap.unsafeFromSOPList
                  [ (n PlutusTx.+ 1, 1)
                  , (n PlutusTx.+ 2, 2)
                  , (n PlutusTx.+ 3, 3)
                  , (n PlutusTx.+ 4, 4)
                  , (n PlutusTx.+ 5, 5)
                  ]
              m2 =
                Data.AssocMap.unsafeFromSOPList
                  [ (n PlutusTx.+ 3, 33)
                  , (n PlutusTx.+ 4, 44)
                  , (n PlutusTx.+ 6, 66)
                  , (n PlutusTx.+ 7, 77)
                  ]
              m = Data.AssocMap.unionWith (PlutusTx.+) m1 m2
           in Data.AssocMap.toSOPList m
        ||]
    )

{-| Similar to map2, but uses 'union' instead of 'unionWith'. Evaluating 'map3' and 'map2'
should yield the same result.
-}
map3 :: CompiledCode (Integer -> [(Integer, Integer)])
map3 =
  $$( compile
        [||
        \n ->
          let m1 =
                Data.AssocMap.unsafeFromSOPList
                  [ (n PlutusTx.+ 1, 1)
                  , (n PlutusTx.+ 2, 2)
                  , (n PlutusTx.+ 3, 3)
                  , (n PlutusTx.+ 4, 4)
                  , (n PlutusTx.+ 5, 5)
                  ]
              m2 =
                Data.AssocMap.unsafeFromSOPList
                  [ (n PlutusTx.+ 3, 30)
                  , (n PlutusTx.+ 4, 40)
                  , (n PlutusTx.+ 6, 60)
                  , (n PlutusTx.+ 7, 70)
                  ]
              m = Data.AssocMap.union m1 m2
              f = these id id (PlutusTx.+)
           in PlutusTx.fmap (PlutusTx.fmap f) (Data.AssocMap.toSOPList m)
        ||]
    )
