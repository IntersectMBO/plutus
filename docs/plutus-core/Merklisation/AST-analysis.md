## Some basic statistics for Plutus Core abstract syntax trees

[kwxm, November 2019]

The table below shows some simple statistics relating to the
(unapplied) validator code for our sample contracts, obtained from
Haskell code using the PlutusTx compilation infrastructure.  The
figures show the number of basic AST nodes for each contract.  The PLC
AST also contains large amounts of type information, but this is not
considered here.  The final column shows the total number of names
occurring in variables and lambda abstractions; types also contain
names, but these are omitted.

Variables, lambda abstractions and applications account for about 80%
of the nodes in the ASTs, with type-level abstraction and application
forming 17-22%.  The remaining types of terms (built-in constants,
built-in function names, the `error` term, and the
type-level `iwrap` and `unwrap` operations) are quite negligible in
comparison, accounting for only 2-3% of nodes between them.  The
figure for built-in functions is misleading however: it appears that
the PlutusTx compiler wraps each built-in function in a lambda
expression and then uses that to apply the function indirectly
whenever it is required.  Thus potentially expensive built-in
functions may be applied much more often than the bare figures
suggest.  No attempt was made here to track how many indirect calls to
built-in functions were made.

There are significant numbers of names in the AST, which currently
contain quite a lot of information including human-readable names.  As
the detailed figures in
[Erasure-merklisation.md](./Erasure-Merklisation.md) show, reducing
the amount of information in names is quite helpful for reducing the
size of serialised code.


| Contract | Total Nodes | Var | Lam | App | Constant | Builtin | Error | TyAbs | TyInst | Wrap | Unwrap | (Names) |
| :---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :---: |
| Crowdfunding | 4663 | 1242 | 1093 | 1320 | 44 | 11 | 24 | 309 | 569 | 21 | 30 | (2335)| 
|       |       |26.6% | 23.4% | 28.3% | 0.9% | 0.2% | 0.5% | 6.6% | 12.2% | 0.5% | 0.6% | - | 
| |
| |
| Currrency | 7309 | 1916 | 1662 | 2059 | 137 | 6 | 1 | 371 | 1109 | 20 | 28 | (3578)| 
|       |       |26.2% | 22.7% | 28.2% | 1.9% | 0.1% | 0.0% | 5.1% | 15.2% | 0.3% | 0.4% | - | 
| |
| |
| Escrow | 5217 | 1394 | 1109 | 1548 | 120 | 11 | 24 | 299 | 664 | 20 | 28 | (2503)| 
|       |       |26.7% | 21.3% | 29.7% | 2.3% | 0.2% | 0.5% | 5.7% | 12.7% | 0.4% | 0.5% | - | 
| |
| |
| Future | 9301 | 2388 | 1762 | 2847 | 426 | 11 | 23 | 468 | 1310 | 26 | 40 | (4150)| 
|       |       |25.7% | 18.9% | 30.6% | 4.6% | 0.1% | 0.2% | 5.0% | 14.1% | 0.3% | 0.4% | - | 
| |
| |
| Game | 4487 | 1201 | 1138 | 1230 | 26 | 3 | 1 | 206 | 667 | 9 | 6 | (2339)| 
|       |       |26.8% | 25.4% | 27.4% | 0.6% | 0.1% | 0.0% | 4.6% | 14.9% | 0.2% | 0.1% | - | 
| |
| |
| GameStateMachine | 5954 | 1438 | 987 | 1858 | 405 | 8 | 8 | 300 | 899 | 21 | 30 | (2425)| 
|       |       |24.2% | 16.6% | 31.2% | 6.8% | 0.1% | 0.1% | 5.0% | 15.1% | 0.4% | 0.5% | - | 
| |
| |
| MultiSig | 5454 | 1442 | 1294 | 1541 | 91 | 8 | 1 | 246 | 807 | 12 | 12 | (2736)| 
|       |       |26.4% | 23.7% | 28.3% | 1.7% | 0.1% | 0.0% | 4.5% | 14.8% | 0.2% | 0.2% | - | 
| |
| |
| MultiSigStateMachine | 9974 | 2583 | 1904 | 3055 | 435 | 12 | 26 | 477 | 1410 | 28 | 44 | (4487)| 
|       |       |25.9% | 19.1% | 30.6% | 4.4% | 0.1% | 0.3% | 4.8% | 14.1% | 0.3% | 0.4% | - | 
| |
| |
| PubKey | 5077 | 1346 | 1234 | 1420 | 68 | 6 | 1 | 226 | 755 | 11 | 10 | (2580)| 
|       |       |26.5% | 24.3% | 28.0% | 1.3% | 0.1% | 0.0% | 4.5% | 14.9% | 0.2% | 0.2% | - | 
| |
| |
| Swap | 8062 | 2229 | 1919 | 2341 | 90 | 14 | 9 | 382 | 1048 | 14 | 16 | (4148)| 
|       |       |27.6% | 23.8% | 29.0% | 1.1% | 0.2% | 0.1% | 4.7% | 13.0% | 0.2% | 0.2% | - | 
| |
| |
| TokenAccount | 2464 | 621 | 602 | 628 | 5 | 3 | 0 | 238 | 322 | 19 | 26 | (1223)| 
|       |       |25.2% | 24.4% | 25.5% | 0.2% | 0.1% | 0.0% | 9.7% | 13.1% | 0.8% | 1.1% | - | 
| |
| |
| Vesting | 4960 | 1321 | 1147 | 1401 | 45 | 12 | 24 | 332 | 621 | 23 | 34 | (2468)| 
|       |       |26.6% | 23.1% | 28.2% | 0.9% | 0.2% | 0.5% | 6.7% | 12.5% | 0.5% | 0.7% | - | 


### Depths of ASTs

The table below shows the depth of the AST for each validator,
together with the "&lambda;-depth": the depth of nesting of Lam nodes
(relevant to de Bruijn indices)

| Contract | Total Nodes | Depth | &lambda;-depth |
| :---: | ---: | ---: | ---: |
| Crowdfunding | 4663 | 325 | 122 |
| Currrency | 7309 | 423 | 175 |
| Escrow | 5217 | 321 | 119 |
| Future | 9301 | 484 | 191 |
| Game | 4487 | 388 | 164 |
| GameStateMachine | 5954 | 356 | 115 |
| MultiSig | 5454 | 386 | 163 |
| MultiSigStateMachine | 9974 | 478 | 190 |
| PubKey | 5077 | 386 | 163 |
| Swap | 8062 | 489 | 218 |
| TokenAccount | 2464 | 198 | 79 |
| Vesting | 4960 | 325 | 135 |

