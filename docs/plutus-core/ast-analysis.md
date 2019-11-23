## Some basic statistics for Plutus Core abstract syntax trees

[kwxm, November 2019]

The table below shows some simple statistics relating to the validator
code for our sample contracts, obtained from Haskell code using the
PlutusTx compilation infrastructure.  The figures show the number of
basic AST nodes for each contract.  The PLC AST also contains large
amounts of type information, but this is not considered here.  The
final column shows the total number of names occurring in variables
and lambda abstractions; types also contain names, but these are
omitted.

Variables, lambda abstractions and applications account for about 80%
of the nodes in the ASTs, with type-level abstraction and application
forming 17-22%.  The remaining types of terms (constants, application
of built-in functions, the `error` term, and the type-level `iwrap`
and `unwrap` operations) are quite negligible in comparison,
accounting for only 2-3% of nodes between them.  The figure for
built-in functions is misleading however: it appears that the PlutusTx
compiler wraps each built-in function in a lambda expression and then
uses that to apply the function indirectly whenever it is required.
Thus potentially expensive built-in functions may be applied much
more often than the bare figures suggest.  No attempt was made here to
track how many indirect calls to built-in functions were made.

There are significant numbers of names in the AST, which currently
contain quite a lot of information including human-readable names.  As
the detailed figures in
[Erasure-merklisation.md](./Erasure-Merklisation.md) show, reducing
the amount of information in names is quite helpful for reducing the
size of serialised code.


| Contract | Total Nodes | Var | Lam | App | Constant | Builtin | Error | TyAbs | TyInst | Wrap | Unwrap | (Names) |
| :---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :---: |
| Crowdfunding | 4606 | 1236 | 1081 | 1314 | 44 | 11 | 24 | 301 | 568 | 21 | 30 | (2317)| 
|       |       |26.8% | 23.5% | 28.5% | 1.0% | 0.2% | 0.5% | 6.5% | 12.3% | 0.5% | 0.7% | - | 
| | | | | | | | | | | | | |
| | | | | | | | | | | | | |
| Currrency | 6864 | 1797 | 1555 | 1938 | 135 | 6 | 1 | 349 | 1036 | 20 | 28 | (3352)| 
|       |       |26.2% | 22.7% | 28.2% | 2.0% | 0.1% | 0.0% | 5.1% | 15.1% | 0.3% | 0.4% | - | 
| | | | | | | | | | | | | |
| | | | | | | | | | | | | |
| Escrow | 5558 | 1503 | 1233 | 1643 | 106 | 11 | 24 | 318 | 690 | 22 | 32 | (2736)| 
|       |       |27.0% | 22.2% | 29.6% | 1.9% | 0.2% | 0.4% | 5.7% | 12.4% | 0.4% | 0.6% | - | 
| | | | | | | | | | | | | |
| | | | | | | | | | | | | |
| Future | 7694 | 2104 | 1885 | 2150 | 37 | 9 | 1 | 390 | 1071 | 20 | 28 | (3989)| 
|       |       |27.3% | 24.5% | 27.9% | 0.5% | 0.1% | 0.0% | 5.1% | 13.9% | 0.3% | 0.4% | - | 
| | | | | | | | | | | | | |
| | | | | | | | | | | | | |
| Game | 4047 | 1082 | 1035 | 1109 | 24 | 3 | 1 | 184 | 595 | 9 | 6 | (2117)| 
|       |       |26.7% | 25.6% | 27.4% | 0.6% | 0.1% | 0.0% | 4.5% | 14.7% | 0.2% | 0.1% | - | 
| | | | | | | | | | | | | |
| | | | | | | | | | | | | |
| GameStateMachine | 5685 | 1375 | 914 | 1794 | 405 | 8 | 7 | 278 | 863 | 20 | 28 | (2289)| 
|       |       |24.2% | 16.1% | 31.6% | 7.1% | 0.1% | 0.1% | 4.9% | 15.2% | 0.4% | 0.5% | - | 
| | | | | | | | | | | | | |
| | | | | | | | | | | | | |
| MultiSig | 4875 | 1290 | 1184 | 1366 | 68 | 8 | 1 | 224 | 711 | 12 | 12 | (2474)| 
|       |       |26.5% | 24.3% | 28.0% | 1.4% | 0.2% | 0.0% | 4.6% | 14.6% | 0.2% | 0.2% | - | 
| | | | | | | | | | | | | |
| | | | | | | | | | | | | |
| MultiSigStateMachine | 9706 | 2524 | 1837 | 2995 | 435 | 12 | 25 | 457 | 1377 | 27 | 42 | (4361)| 
|       |       |26.0% | 18.9% | 30.9% | 4.5% | 0.1% | 0.3% | 4.7% | 14.2% | 0.3% | 0.4% | - | 
| | | | | | | | | | | | | |
| | | | | | | | | | | | | |
| PubKey | 4636 | 1227 | 1130 | 1299 | 66 | 6 | 1 | 204 | 683 | 11 | 10 | (2357)| 
|       |       |26.5% | 24.4% | 28.0% | 1.4% | 0.1% | 0.0% | 4.4% | 14.7% | 0.2% | 0.2% | - | 
| | | | | | | | | | | | | |
| | | | | | | | | | | | | |
| Swap | 7611 | 2110 | 1813 | 2220 | 88 | 14 | 9 | 360 | 976 | 14 | 16 | (3923)| 
|       |       |27.7% | 23.8% | 29.2% | 1.2% | 0.2% | 0.1% | 4.7% | 12.8% | 0.2% | 0.2% | - | 
| | | | | | | | | | | | | |
| | | | | | | | | | | | | |
| TokenAccount | 2433 | 615 | 592 | 622 | 5 | 3 | 0 | 230 | 321 | 19 | 26 | (1207)| 
|       |       |25.3% | 24.3% | 25.6% | 0.2% | 0.1% | 0.0% | 9.5% | 13.2% | 0.8% | 1.1% | - | 
| | | | | | | | | | | | | |
| | | | | | | | | | | | | |
| Vesting | 8334 | 2279 | 2029 | 2344 | 33 | 8 | 25 | 420 | 1167 | 22 | 32 | (4308)| 
|       |       |27.3% | 24.3% | 28.1% | 0.4% | 0.1% | 0.3% | 5.0% | 14.0% | 0.3% | 0.4% | - | 
