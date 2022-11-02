-- editorconfig-checker-disable-file
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}

module Large (alfaSig,bnfcSig,javaSig) where

import AlgTypes

list = [declExp| list = all a.(1 + (a * (list a))) |]

-- type generated (I suppose) by BNFC for the Alfa grammar at
-- https://github.com/BNFC/bnfc/blob/master/examples/Alfa/Alfa.cf

alfaSig = algSignature (map algDecl [list,alfa1,alfa2,alfa3,alfa4,alfa5,alfa6,alfa7,alfa8,alfa9,alfa10,alfa11,alfa12,alfa13,alfa14,alfa15,alfa16,alfa17])

alfa1 = [declExp| module = list decl |]

alfa2 = [declExp| decl = ((list defAttr) * def) + import |]

alfa3 = [declExp| def = (1 * (list varDecl) * exp * exp)
                      + (1 * exp)
                      + (1 * (list typing) * packageBody)
                      + (exp * (list openArg))
                      + (1 * (list typing) * (list constructor))
                      + (1 * (list typing) * exp)
                      + (1 * (list typing) * exp)
                      + (list def)
                      + comment |]

alfa4 = [declExp| exp = 1
                      + 1
                      + 1
                      + 1
                      + 1
                      + 1
                      + 1
                      + 1
                      + 1
                      + 1
                      + 1
                      + (exp * 1)
                      + (exp * exp)
                      + (exp * 1 * exp)
                      + (list fieldDecl)
                      + (list binding)
                      + (list constructor)
                      + (varDecl * arrow * exp)
                      + (exp * arrow * exp)
                      + (varDecl * arrow * exp)
                      + ((list 1) * arrow * exp)
                      + ((list decl) * exp)
                      + (exp * (list openArg) * exp)
                      + (exp * (list branch))
                      + ((list varDecl) * (list indConstructor))
                      + (comment * exp)
                      + (exp * comment)
                      + 1
                      + integer
                      |]


alfa5 = [declExp| arrow = 1 + 1|]

alfa6 = [declExp| typing = varDecl + exp|]

alfa7 = [declExp| varDecl = (list bound) * exp|]

alfa8 = [declExp| bound = 1 + 1|]

alfa9 = [declExp| fieldDecl = 1 * exp|]

alfa10 = [declExp| branch = (1 * (list 1) * exp)
                          + (1 * 1 * 1 * exp)
                          + (1 * exp) |]

alfa11 = [declExp| constructor = (1 * (list typing))
                               + 1 |]

alfa12 = [declExp| indConstructor = (1 * (list typing) * (list exp)) |]

alfa13 = [declExp| binding = 1 * exp|]

alfa14 = [declExp| packageBody = (list decl) * exp|]

alfa15 = [declExp| openArg = ((list defAttr) * 1)
                           + ((list defAttr) * 1 * exp)
                           + ((list defAttr) * 1 * exp)
                           + ((list defAttr) * 1 * exp * exp) |]

alfa16 = [declExp| defAttr = 1 + 1 + 1 + 1|]

alfa17 = [declExp| import = 1|]


-- type generated (I suppose) by bnfc for the bnfc grammar
-- at https://github.com/BNFC/bnfc/blob/master/examples/LBNF/LBNF.cf

bnfcSig = algSignature (map algDecl [list,bnfc1,bnfc2,bnfc3,bnfc4,bnfc5,bnfc6,bnfc7,bnfc8,bnfc9,bnfc10,bnfc11])

bnfc1 = [declExp| def = label * cat * (list item) |]

bnfc2 = [declExp| item = 1 + cat|]

bnfc3 = [declExp| cat = cat + 1|]

bnfc4 = [declExp| label = 1 + (1 * (list profItem))
                        + (1 * 1 * (list profItem))
                        + (1 * 1)|]

bnfc5 = [declExp| profItem = (list 1) * (list 1)|]

bnfc6 = [declExp| def = 1 + (1 * 1)
                      + (label * cat * (list item))
                      + (1 * reg)
                      + (list 1)
                      + (minimumSize * cat * 1)
                      + (minimumSize * cat * 1)
                      + (1 * 1)
                      + (1 * (list rhs))
                      + (list 1)
                      + (list 1)
                      + 1 |]

bnfc7 = [declExp| rhs = (list 1) |]

bnfc8 = [declExp| minimumSize = 1 + 1|]

bnfc9 = [declExp| reg2 = reg2 reg3 |]

bnfc10 = [declExp| reg1 = (reg1 * reg2) + (reg2 * reg2)|]

bnfc11 = [declExp| reg3 = 1 + 1 + 1 + 1 + 1 + 1 + 1
                        + 1 + 1 + 1 + 1 + 1 |]

-- as above, for the java grammar at http://people.cs.uchicago.edu/~mrainey/java.cf

javaSig = algSignature (map algDecl [java1,java2,java3,java4,java5,java6,java7,java8,java9,java10,java11,java12,java13,java14,java15,java16,java17,java18,java19,java20,java21,java22,java23,java24,java25,java26,java27,java28,java29,java30,java31,java32,java33,java34,java35])

java1 = [declExp| programFile = ((list 1) * (list 1)
                              * (list import) * (list typeDecl))
                              + ((list import) * (list typeDecl))|]

java2 = [declExp| import = ((list ident) * (list 1))
                         + ((list ident) * (list 1))|]

java3 = [declExp| typeDecl = classHeader * (list fileDeclaration)|]

java4 = [declExp| classHeader = ((list modifier) * 1)
                              + ((list modifier) * 1 * (list typeName))
                              + ((list modifier) * 1)
                              + ((list modifier) * 1 * (list typeName))
                              + ((list modifier) * 1)
                              + ((list modifier) * 1 * (list typeName))
                              + ((list modifier) * 1 * (list typeName))
                              + ((list modifier) * 1 * (list typeName) * (list typeName)) |]

java5 = [declExp| fieldDeclaration =
                    ((list modifier) * typeSpec * (list varDecl))
                  + ((list modifier) * typeSpec * methodDecl * methodBody)
                  + ((list modifier) * typeSpec * methodDecl * (list typeName) * methodBody)
                  + ((list modifier) * 1 * (list parameter) * body)
                  + ((list modifier) * 1 * (list parameter) * (list typeName) * body)
                  + body
                  + typeDecl
                  + body |]

java6 = [declExp| methodBody = 1 + body |]

java7 = [declExp| lVarStatement =
                   (typeSpec * (list varDecl))
                 + (typeSpec * (list varDecl))
                 + stm + 1 |]

java8 = [declExp| body = (list lVarStatement) |]

java9 = [declExp| stm = 1 + 1 + exp + 1 + exp
                      + (list lVarStatement)
                      + jumpStm + guardStm
                      + iterStm + selectionStm |]

java10 = [declExp| declaratorName = 1 + (list bracketsOpt) |]

java11 = [declExp| varDecl = (declaratorName * variableInits)                            + 1 |]

java12 = [declExp| variableInits = exp + 1 + arrayInits|]

java13 = [declExp| arrayInits = variableInits
                              + (arrayInits * variableinits)
                              + arrayInits |]

java14 = [declExp| methodDecl = (declaratorName * (list parameter))
                              + (methodDecl * bracketsOpt)|]

java15 = [declExp| parameter = (typeSpec * declaratorName)
                             + (typeSpec * declaratorName) |]

java16 = [declExp| selectionStm = (exp * stm * (list elseIf))
                                + (exp * stm * (list elseIf) * stm)
                                + (exp * body)|]

java17 = [declExp| elseIf = exp * stm |]

java18 = [declExp| jumpStm = 1 + (1 * 1) + 1 + (1 * 1) + 1
                           + (1 * exp) + (1 * exp)|]
java19 = [declExp| guardStm = (exp * body)
                            + (body * (list catch))
                            + (body * (list catch) * body)|]

java20 = [declExp| catch = (typeSpec * 1 * body)
                         + (typeSpec * body)|]
java21 = [declExp| iterStm = (exp * stm)
                           + (stm * exp)
                           + (forInit * (list exp) * (list exp) * stm)
                           + (list exp)
                           + (typeSpec * (list varDecl))
                           + (typeSpec * (list varDecl))|]

java22 = [declExp| forInit = (list exp)
                           + (typeSpec * (list varDecl))
                           + (typeSpec * (list varDecl))|]

java23 = [declExp| modifier = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 |]

java24 = [declExp| typeSpec = (typeName * (list bracketsOps))
                            + typeName |]

java25 = [declExp| typeName = 1 + (list 1) |]

java26 = [declExp| bracketsOpt = 1|]

java27 = [declExp| exp = (exp * 1 * exp)
                       + (exp * typeName)
                       + (exp * exp * exp)
                       + (exp * exp)
                       + (exp * exp)
                       + (exp * exp)
                       + (exp * exp)
                       + (exp * exp)
                       + (exp * exp)
                       + (exp * exp)
                       + (exp * exp)
                       + (exp * exp)
                       + (exp * exp)
                       + (basicType * exp)
                       + (exp * exp)
                       + ((list 1) * (list bracketsOpt) * exp)
                       + (1 * exp)
                       + exp + exp
                       + exp + exp
                       + 1 + arrAcc
                       + mthCall
                       + fieldAcc
                       + 1
                       + 1
                       + newAllow
                       + (list 1)|]

java28 = [declExp| newAlloc = (typeName * args)
                            + (typeName * args * (list fieldDeclaration))
                            + (typeName * (list dimExpr))
                            + (typeName * (list dimExpr))
                            + (typeName * (list dimExpr) * arrayInits)|]

java29 = [declExp| arrAcc = ((list 1)  * exp) + (specExp * exp)|]

java30 = [declExp| specExp = exp + specExpNp + 1|]

java31 = [declExp| specExpNp = 1 + arrAcc + mthCall + fieldAcc |]

java32 = [declExp| mthCall = ((list 1) * args)
                           + (specExpNp * args)
                           + (1 * args)|]

java33 = [declExp| fieldAcc = (specExp * 1)
                            + (newAlloc * 1)
                            + (list 1) + (list 1)
                            + basicType|]
java34 = [declExp| args = list exp|]

java35 = [declExp| dimExpr = exp|]


