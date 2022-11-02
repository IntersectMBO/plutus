## Experiments with a shared fixpoint combinator


The table below shows the results of some compression tests on
contract validators compiled by a version of the Plutus compiler (due
to @michaelpj) which shares the fixpoint combinator instead of
creating multiple copies.  It corresponds to the table in
[Erasure.md](./Erasure.md) (the validator sources should be exactly
the same).

Sharing the fixpoint combinator saves about 2-15% on the size of the
uncompressed serialised validators.  This is inherited by the various
transformations of the AST, but it seems to make the compressed versions
slightly bigger.


| Contract | Compression | Typed | Typed, stringless names | Untyped | Untyped, stringless names | Untyped, integer IDs only | Untyped, de Bruijn | Untyped, de Bruijn, annotations not serialised
| :---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Crowdfunding | Uncompressed | 92950 | 56872 | 25070 | 13569 | 11648 (12.5%) | 8715 (9.4%) | 5558 | 
|    | Compressed | 16765 | 13497 | 6071 | 4202 | 4124 (4.4%) | 1722 (1.9%) | 1562 | 
| |
| |
| Currrency | Uncompressed | 143275 | 85924 | 44291 | 22773 | 19577 (13.7%) | 15042 (10.5%) | 9701 | 
|    | Compressed | 24583 | 19940 | 9448 | 6825 | 6723 (4.7%) | 3265 (2.3%) | 3024 | 
| |
| |
| Escrow | Uncompressed | 101659 | 62466 | 28431 | 15545 | 13424 (13.2%) | 10452 (10.3%) | 6698 | 
|    | Compressed | 17669 | 14388 | 6327 | 4461 | 4379 (4.3%) | 2079 (2.0%) | 1901 | 
| |
| |
| Future | Uncompressed | 184184 | 117130 | 50370 | 28196 | 24620 (13.4%) | 19495 (10.6%) | 12478 | 
|    | Compressed | 33480 | 27796 | 10941 | 7698 | 7596 (4.1%) | 3721 (2.0%) | 3437 | 
| |
| |
| Game | Uncompressed | 98766 | 55818 | 32492 | 15605 | 13296 (13.5%) | 10145 (10.3%) | 6561 | 
|    | Compressed | 16556 | 13189 | 6653 | 4701 | 4622 (4.7%) | 2330 (2.4%) | 2149 | 
| |
| |
| GameStateMachine | Uncompressed | 100107 | 63148 | 28647 | 16905 | 14894 (14.9%) | 12447 (12.4%) | 7962 | 
|    | Compressed | 17492 | 14100 | 6058 | 4201 | 4129 (4.1%) | 2190 (2.2%) | 2004 | 
| |
| |
| MultiSig | Uncompressed | 107636 | 61556 | 36801 | 18242 | 15632 (14.5%) | 12119 (11.3%) | 7834 | 
|    | Compressed | 18319 | 14563 | 7696 | 5450 | 5350 (5.0%) | 2782 (2.6%) | 2561 | 
| |
| |
| MultiSigStateMachine | Uncompressed | 171590 | 107726 | 53632 | 30118 | 26269 (15.3%) | 20849 (12.2%) | 13362 | 
|    | Compressed | 30306 | 24794 | 11405 | 8147 | 8048 (4.7%) | 4079 (2.4%) | 3756 | 
| |
| |
| PubKey | Uncompressed | 103604 | 58877 | 35069 | 17182 | 14696 (14.2%) | 11351 (11.0%) | 7344 | 
|    | Compressed | 17419 | 13846 | 7252 | 5140 | 5056 (4.9%) | 2613 (2.5%) | 2415 | 
| |
| |
| Swap | Uncompressed | 148566 | 85490 | 54976 | 27601 | 23643 (15.9%) | 18020 (12.1%) | 11603 | 
|    | Compressed | 26049 | 20637 | 11904 | 8521 | 8379 (5.6%) | 4058 (2.7%) | 3761 | 
| |
| |
| TokenAccount | Uncompressed | 62982 | 39355 | 10916 | 5864 | 4991 (7.9%) | 3642 (5.8%) | 2309 | 
|    | Compressed | 11856 | 9631 | 3275 | 2050 | 2025 (3.2%) | 758 (1.2%) | 680 | 
| |
| |
| Vesting | Uncompressed | 99739 | 61647 | 25795 | 14073 | 12083 (12.1%) | 9048 (9.1%) | 5771 | 
|    | Compressed | 17929 | 14623 | 6250 | 4385 | 4309 (4.3%) | 1811 (1.8%) | 1638 | 

