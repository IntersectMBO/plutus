{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -ddump-splices #-}

{-# HLINT ignore "Use guards" #-}

module TH.Unroll.Spec.Lib where

import PlutusTx.Prelude

fibonacci :: Integer -> Integer
fibonacci n =
  if n == 0 || n == 1
    then 1
    else fibonacci (n - 1) + fibonacci (n - 2)
{-# INLINEABLE fibonacci #-}

-- Example of unrolling fibonacci function manually 3 levels down
fibonacciManuallyUnrolled3 :: Integer -> Integer
fibonacciManuallyUnrolled3 n =
  if n == 0 || n == 1
    then n
    else
      ( let
          n' = n - 1
         in
          if n' == 0 || n' == 1
            then n'
            else
              ( let
                  n'' = n' - 1
                 in
                  if n'' == 0 || n'' == 1
                    then n''
                    else
                      ( let n''' = n'' - 1
                         in if n''' == 0 || n''' == 1
                              then n'''
                              else
                                fibonacciManuallyUnrolled3 (n''' - 1)
                                  + fibonacciManuallyUnrolled3 (n''' - 2)
                      )
                        + let n''' = n'' - 2
                           in if n''' == 0 || n''' == 1
                                then n'''
                                else
                                  fibonacciManuallyUnrolled3 (n''' - 1)
                                    + fibonacciManuallyUnrolled3 (n''' - 2)
              )
                + let
                    n'' = n' - 2
                   in
                    if n'' == 0 || n'' == 1
                      then n''
                      else
                        ( let n''' = n'' - 1
                           in if n''' == 0 || n''' == 1
                                then n'''
                                else
                                  fibonacciManuallyUnrolled3 (n''' - 1)
                                    + fibonacciManuallyUnrolled3 (n''' - 2)
                        )
                          + let n''' = n'' - 2
                             in if n''' == 0 || n''' == 1
                                  then n'''
                                  else
                                    fibonacciManuallyUnrolled3 (n''' - 1)
                                      + fibonacciManuallyUnrolled3 (n''' - 2)
      )
        + let
            n' = n - 2
           in
            if n' == 0 || n' == 1
              then n'
              else
                ( let
                    n'' = n' - 1
                   in
                    if n'' == 0 || n'' == 1
                      then n''
                      else
                        ( let n''' = n'' - 1
                           in if n''' == 0 || n''' == 1
                                then n'''
                                else
                                  fibonacciManuallyUnrolled3 (n''' - 1)
                                    + fibonacciManuallyUnrolled3 (n''' - 2)
                        )
                          + let n''' = n'' - 2
                             in if n''' == 0 || n''' == 1
                                  then n'''
                                  else
                                    fibonacciManuallyUnrolled3 (n''' - 1)
                                      + fibonacciManuallyUnrolled3 (n''' - 2)
                )
                  + let
                      n'' = n' - 2
                     in
                      if n'' == 0 || n'' == 1
                        then n''
                        else
                          ( let n''' = n'' - 1
                             in if n''' == 0 || n''' == 1
                                  then n'''
                                  else
                                    fibonacciManuallyUnrolled3 (n''' - 1)
                                      + fibonacciManuallyUnrolled3 (n''' - 2)
                          )
                            + let n''' = n'' - 2
                               in if n''' == 0 || n''' == 1
                                    then n'''
                                    else
                                      fibonacciManuallyUnrolled3 (n''' - 1)
                                        + fibonacciManuallyUnrolled3 (n''' - 2)
{-# INLINEABLE fibonacciManuallyUnrolled3 #-}

-- Fibonacci function with fix
fibonacciFix :: Integer -> Integer
fibonacciFix = fix $ \self n ->
  if n == 0 || n == 1
    then n
    else self (n - 1) + self (n - 2)
{-# INLINEABLE fibonacciFix #-}

-- Example of unrolling fibonacci function with fix manually 3 levels down
fibonacciFixManuallyUnrolled3 :: Integer -> Integer
fibonacciFixManuallyUnrolled3 =
  fix $ \self n ->
    if n == 0 || n == 1
      then n
      else
        ( let
            n' = n - 1
           in
            if n' == 0 || n' == 1
              then n'
              else
                ( let
                    n'' = n' - 1
                   in
                    if n'' == 0 || n'' == 1
                      then n''
                      else
                        ( let n''' = n'' - 1
                           in if n''' == 0 || n''' == 1
                                then n'''
                                else self (n''' - 1) + self (n''' - 2)
                        )
                          + let n''' = n'' - 2
                             in if n''' == 0 || n''' == 1
                                  then n'''
                                  else self (n''' - 1) + self (n''' - 2)
                )
                  + let
                      n'' = n' - 2
                     in
                      if n'' == 0 || n'' == 1
                        then n''
                        else
                          ( let n''' = n'' - 1
                             in if n''' == 0 || n''' == 1
                                  then n'''
                                  else self (n''' - 1) + self (n''' - 2)
                          )
                            + let n''' = n'' - 2
                               in if n''' == 0 || n''' == 1
                                    then n'''
                                    else self (n''' - 1) + self (n''' - 2)
        )
          + let
              n' = n - 2
             in
              if n' == 0 || n' == 1
                then n'
                else
                  ( let
                      n'' = n' - 1
                     in
                      if n'' == 0 || n'' == 1
                        then n''
                        else
                          ( let n''' = n'' - 1
                             in if n''' == 0 || n''' == 1
                                  then n'''
                                  else self (n''' - 1) + self (n''' - 2)
                          )
                            + let n''' = n'' - 2
                               in if n''' == 0 || n''' == 1
                                    then n'''
                                    else self (n''' - 1) + self (n''' - 2)
                  )
                    + let
                        n'' = n' - 2
                       in
                        if n'' == 0 || n'' == 1
                          then n''
                          else
                            ( let n''' = n'' - 1
                               in if n''' == 0 || n''' == 1
                                    then n'''
                                    else self (n''' - 1) + self (n''' - 2)
                            )
                              + let n''' = n'' - 2
                                 in if n''' == 0 || n''' == 1
                                      then n'''
                                      else self (n''' - 1) + self (n''' - 2)
{-# INLINEABLE fibonacciFixManuallyUnrolled3 #-}
