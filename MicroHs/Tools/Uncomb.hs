{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Uncomb where
import Data.Char
import Data.Data (Data)
import Data.Generics.Uniplate.Data

infixl :@
data Exp
  = S | S' | K | A | U | I | Y | B | B' | Z | C | C' | P | R | O | K2 | K3 | K4 | C'B
  | Add | Sub | Lt
  | Exp :@ Exp | Int Integer | Label Int Exp | Ref Int | Tick String | Vx | Vy | Vz | Vw
  deriving (Show, Read, Data, Eq, Ord)

reduce :: Exp -> Exp
reduce (((S :@ x) :@ y) :@ z)                    = (x :@ z) :@ (y :@ z)
reduce ((((S' :@ x) :@ y) :@ z) :@ w)            = (x :@ (y :@ w)) :@ (z :@ w)
reduce ((K :@ x) :@ _y)                          = x
reduce ((A :@ _x) :@ y)                          = y
reduce ((U :@ x) :@ y)                           = y :@ x
reduce (I :@ x)                                  = x
reduce (((B :@ x) :@ y) :@ z)                    = x :@ (y :@ z)
reduce ((((B' :@ x) :@ y) :@ z) :@ w)            = (x :@ y) :@ (z :@ w)
reduce (((Z :@ x) :@ y) :@ _z)                   = x :@ y
reduce (((C :@ x) :@ y) :@ z)                    = (x :@ z) :@ y
reduce ((((C' :@ x) :@ y) :@ z) :@ w)            = (x :@ (y :@ w)) :@ z
reduce (((P :@ x) :@ y) :@ z)                    = (z :@ x) :@ y
reduce (((R :@ x) :@ y) :@ z)                    = (y :@ z) :@ x
reduce ((((O :@ x) :@ y) :@ z) :@ w)             = (w :@ x) :@ y
reduce (((K2 :@ x) :@ _y) :@ _z)                 = x
reduce ((((K3 :@ x) :@ _y) :@ _z) :@ _w)         = x
reduce (((((K4 :@ x) :@ _y) :@ _z) :@ _w) :@ _v) = x
reduce ((((C'B :@ x) :@ y) :@ z) :@ w)           = (x :@ z) :@ (y :@ w)
reduce (Label _ e)                               = e
reduce (Tick _ :@ e)                             = e
reduce e                                         = e

parseExp :: String -> (Exp, String)
parseExp (' ':cs) = parseExp cs
parseExp ('(':cs) = (e1 :@ e2, r'')
  where (e1, r) = parseExp cs
        (e2, r') = parseExp r
        r'' = case r' of (')':s) -> s; _ -> error ")"
parseExp ('#':cs) = (Int (read n), r) where (n, r) = span isDigit cs
parseExp (':':cs) = (Label (read n) e, r') where (n, r) = span isDigit cs; (e, r') = parseExp r
parseExp ('_':cs) = (Ref (read n), r) where (n, r) = span isDigit cs
parseExp ('!':'"':cs) = (Tick (init n), drop 1 r) where (n, r) = span (/= '"') cs
parseExp ('+':cs) = (Add, cs)
parseExp ('-':cs) = (Sub, cs)
parseExp ('<':cs) = (Lt, cs)
parseExp ('C':'\'':'B':cs) = (C'B, cs)
parseExp ('S':'\'':cs) = (S', cs)
parseExp ('C':'\'':cs) = (C', cs)
parseExp ('B':'\'':cs) = (B', cs)
parseExp ('K':'2':cs) = (K2, cs)
parseExp ('K':'3':cs) = (K3, cs)
parseExp ('K':'4':cs) = (K4, cs)
parseExp ('S':cs) = (S, cs)
parseExp ('K':cs) = (K, cs)
parseExp ('A':cs) = (A, cs)
parseExp ('U':cs) = (U, cs)
parseExp ('I':cs) = (I, cs)
parseExp ('Y':cs) = (Y, cs)
parseExp ('B':cs) = (B, cs)
parseExp ('Z':cs) = (Z, cs)
parseExp ('C':cs) = (C, cs)
parseExp ('P':cs) = (P, cs)
parseExp ('R':cs) = (R, cs)
parseExp ('O':cs) = (O, cs)
parseExp ('x':cs) = (Vx, cs)
parseExp cs = error $ "parseExp: " ++ show (take 20 cs)

readExp :: String -> Exp
readExp s =
  case parseExp s of
    (e, "") -> e
    x       -> error $ "readExp: " ++ show x

red :: Exp -> Exp
red = transform reduce

s1 = "(U (K ((B C) (P #111))))"
t1 = readExp s1

s2 = "((C ((C (U ((C'B (B' P)) ((B (C' C)) (C P))))) A)) #111)"
t2 = readExp s2

s3 = "((C B) (C (U (K2 A))))"
t3 = readExp s3

s4 = "(:942 ((C ((S ((C <) #2)) (((C' +) (((S' +) ((B :491 ((B !\"F.nfib\") _942)) :4157 ((C -) #1))) ((B _491) ((C -) #2)))) #1))) #1) (_4157 #3))"
t4 = readExp s4

s5 = "(:942 ((C ((S ((C <) #2)) (((C' +) (((S' +) ((B :491 ((B !\"F.nfib\") _942)) :4157 ((C -) #1))) ((B _491) ((C -) #2)))) #1))) #1) x)"
t5 = readExp s5
