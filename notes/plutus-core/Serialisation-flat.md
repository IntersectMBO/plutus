# Serialisation and the `flat` format.

The figures in eg, [Erasure.md](./Merklisation/Erasure.md) show that the sizes
of serialised Plutus Core scripts can be reduced considerably by compression.
However, it was decided that compression methods such as `gzip` shouldn't be
used on the chain because of the risk of vulnerabilities in the standard
implementations.  As an alternative, we decided to switch to the
[flat](https://hackage.haskell.org/package/flat) format instead.  `CBOR`
requires at least one byte for every integer, but in Plutus Core scripts many
numbers are very small (see the figures [here](Merklisation/Compressibility.md)):
`flat` is bit-oriented and produces significantly smaller serialised scripts.

The `CBOR` and `flat` encodings for Plutus Core coexisted for a considerable
time, but the `CBOR` version was eventually removed in [PR 3521](https://github.com/input-output-hk/plutus/pull/3521).
This also removed  some benchmarks (in `plutus-benchmark/flat`)
comparing the time and size performance of different serialisation methods.
For reference, here are the results of these at commit
[abeb9b2](https://github.com/input-output-hk/plutus/commit/abeb9d26f1f9db206dd723b669d3c37e7516efb0)
on the reference machine used for benchmarking (a machine with eight Intel Xeon CPUs (E3-1240 v5 @ 3.50GHz)
and 32GB of memory, running `NixOS 19.09pre-git (Loris)` with the `Linux 4.19.95` kernel).

## Benchmark results
The results below show comparisons of time and space figures for deserialisation
and serialisation of a number of Plutus validation scripts.  Figures are included
for both `flat` and `CBOR` versions with three compression methods:

 1. no compression
 2. compressed with [zlib](https://hackage.haskell.org/package/zlib),
    a Haskell interface to the C [zlib](https://en.wikipedia.org/wiki/Zlib) implementaion
 2. compressed with [pure-zlib](https://hackage.haskell.org/package/pure-zlib),
    as Haskell-only zlib implementation

Results are given for two versions of Plutus Core ASTs: one using the `Name`
type for variables and one using de Bruijn indices, which lead to more compact
serialised scripts.

## Times

(Edited Criterion output, showing the `time` figure)


### Deserialisation times: de Bruijn-indexed ASTs
| Script       | flat     | flat-zlib | flat-pure-zlib | cbor | cbor-zlib | cbor-pure-zlib |
|:------------ |:--------:|:---------:|:--------------:|:----:|:---------:|:--------------:|
| game         | 1.911 ms | 2.052 ms | 7.054 ms | 3.629 ms | 3.655 ms | 11.56 ms |
| crowdfunding | 989.6 μs | 1.068 ms | 3.511 ms | 1.800 ms | 1.836 ms | 5.912 ms |
| marlowe      | 5.294 ms | 5.484 ms | 20.71 ms | 10.09 ms | 10.43 ms | 31.08 ms |
| vesting      | 1.190 ms | 1.231 ms | 4.556 ms | 2.135 ms | 2.245 ms | 7.064 ms |
| escrow       | 1.175 ms | 1.232 ms | 4.350 ms | 2.106 ms | 2.167 ms | 7.063 ms |
| future       | 2.185 ms | 2.348 ms | 8.482 ms | 4.055 ms | 4.074 ms | 13.67 ms | 

### Deserialisation times: ASTs with `Names`
| Script       | flat     | flat-zlib | flat-pure-zlib | cbor | cbor-zlib | cbor-pure-zlib |
|:------------ |:--------:|:---------:|:--------------:|:----:|:---------:|:--------------:|
| game         | 3.004 ms | 3.123 ms | 17.11 ms | 4.074 ms | 4.333 ms | 21.30 ms |
| crowdfunding | 1.592 ms | 1.670 ms | 8.864 ms | 2.080 ms | 2.210 ms | 11.02 ms |
| marlowe      | 8.139 ms | 8.747 ms | 44.31 ms | 11.76 ms | 11.88 ms | 62.51 ms |
| vesting      | 1.900 ms | 2.035 ms | 10.99 ms | 2.582 ms | 2.714 ms | 13.85 ms |
| escrow       | 1.945 ms | 2.015 ms | 11.19 ms | 2.590 ms | 2.764 ms | 13.76 ms |
| future       | 3.554 ms | 3.722 ms | 20.39 ms | 4.830 ms | 5.061 ms | 26.36 ms |

### Serialisation times: de Bruijn-indexed ASTs
| Script       | flat     | flat-zlib | flat-pure-zlib | cbor | cbor-zlib | cbor-pure-zlib |
|:------------ |:--------:|:---------:|:--------------:|:----:|:---------:|:--------------:|
| game         | 2.187 ms | 2.633 ms | 2.610 ms | 2.261 ms | 3.465 ms | 3.484 ms |
| crowdfunding | 872.9 μ | 1.145 ms | 1.120 ms | 912.2 μ | 1.512 ms | 1.536 ms |
| marlowe      | 7.503 ms | 9.107 ms | 9.017 ms | 7.204 ms | 10.86 ms | 10.83 ms |
| vesting      | 1.151 ms | 1.393 ms | 1.431 ms | 1.098 ms | 1.923 ms | 1.889 ms |
| escrow       | 1.109 ms | 1.396 ms | 1.415 ms | 1.105 ms | 1.889 ms | 1.874 ms |
| future       | 2.608 ms | 3.166 ms | 3.153 ms | 2.423 ms | 4.039 ms | 4.097 ms |

### Serialisation times: ASTs with `Names`
| Script       | flat     | flat-zlib | flat-pure-zlib | cbor | cbor-zlib | cbor-pure-zlib |
|:------------ |:--------:|:---------:|:--------------:|:----:|:---------:|:--------------:|
| game         | 3.037 ms | 5.133 ms | 5.185 ms | 3.032 ms | 6.200 ms | 6.177 ms |
| crowdfunding | 1.376 ms | 2.237 ms | 2.281 ms | 1.373 ms | 2.967 ms | 2.927 ms |
| marlowe      | 9.493 ms | 16.37 ms | 16.30 ms | 9.285 ms | 18.25 ms | 18.22 ms |
| vesting      | 1.756 ms | 2.981 ms | 2.925 ms | 1.793 ms | 3.754 ms | 3.806 ms |
| escrow       | 1.743 ms | 2.940 ms | 2.950 ms | 1.743 ms | 3.758 ms | 3.749 ms |
| future       | 3.763 ms | 6.503 ms | 6.627 ms | 3.604 ms | 7.577 ms | 7.458 ms |


### Sizes
```

** Contract: crowdfunding-indices **
Codec            Size    Of minimum   Of maximum
cbor-pure-zlib   3598    1.0          0.27226636
cbor-zlib        3598    1.0          0.27226636
flat-pure-zlib   3809    1.0586437    0.28823307
flat-zlib        3809    1.0586437    0.28823307
flat             6216    1.7276264    0.47037458
cbor             13215   3.6728737    1.0       

** Contract: crowdfunding-names **
Codec            Size    Of minimum   Of maximum
flat-pure-zlib   7377    1.0          0.3279687 
flat-zlib        7377    1.0          0.3279687 
cbor-pure-zlib   8513    1.1539922    0.3784733 
cbor-zlib        8513    1.1539922    0.3784733 
flat             18045   2.4461162    0.8022496 
cbor             22493   3.0490716    1.0       

** Contract: escrow-indices **
Codec            Size    Of minimum   Of maximum
cbor-pure-zlib   4466    1.0          0.27870694
cbor-zlib        4466    1.0          0.27870694
flat-pure-zlib   4768    1.0676221    0.29755366
flat-zlib        4768    1.0676221    0.29755366
flat             7719    1.7283922    0.48171493
cbor             16024   3.5879982    1.0       

** Contract: escrow-names **
Codec            Size    Of minimum   Of maximum
flat-pure-zlib   9263    1.0          0.33532435
flat-zlib        9263    1.0          0.33532435
cbor-pure-zlib   10619   1.1463889    0.3844121 
cbor-zlib        10619   1.1463889    0.3844121 
flat             22006   2.3756883    0.79662615
cbor             27624   2.9821873    1.0       

** Contract: future-indices **
Codec            Size    Of minimum   Of maximum
cbor-pure-zlib   8604    1.0          0.2941438 
cbor-zlib        8604    1.0          0.2941438 
flat-pure-zlib   9502    1.1043701    0.3248436 
flat-zlib        9502    1.1043701    0.3248436 
flat             15070   1.751511     0.5151961 
cbor             29251   3.3996978    1.0       

** Contract: future-names **
Codec            Size    Of minimum   Of maximum
flat-pure-zlib   17216   1.0          0.33802596
flat-zlib        17216   1.0          0.33802596
cbor-pure-zlib   19947   1.1586316    0.39164752
cbor-zlib        19947   1.1586316    0.39164752
flat             40245   2.337651     0.7901867 
cbor             50931   2.9583528    1.0       

** Contract: game-indices **
Codec            Size    Of minimum   Of maximum
cbor-pure-zlib   6863    1.0          0.28491366
cbor-zlib        6863    1.0          0.28491366
flat-pure-zlib   7736    1.1272038    0.32115576
flat-zlib        7736    1.1272038    0.32115576
flat             12210   1.7791053    0.50689137
cbor             24088   3.5098352    1.0       

** Contract: game-names **
Codec            Size    Of minimum   Of maximum
flat-pure-zlib   14052   1.0          0.33358654
flat-zlib        14052   1.0          0.33358654
cbor-pure-zlib   16185   1.1517934    0.38422278
cbor-zlib        16185   1.1517934    0.38422278
flat             33281   2.3684173    0.79007214
cbor             42124   2.9977226    1.0       

** Contract: marlowe-indices **
Codec            Size    Of minimum   Of maximum
cbor-pure-zlib   18152   1.0          0.270687  
cbor-zlib        18152   1.0          0.270687  
flat-pure-zlib   20817   1.1468158    0.31042814
flat-zlib        20817   1.1468158    0.31042814
flat             34087   1.8778647    0.5083136 
cbor             67059   3.6943038    1.0       

** Contract: marlowe-names **
Codec            Size     Of minimum   Of maximum
flat-pure-zlib   37065    1.0          0.31365034
flat-zlib        37065    1.0          0.31365034
cbor-pure-zlib   44099    1.1897748    0.37317324
cbor-zlib        44099    1.1897748    0.37317324
flat             94332    2.5450425    0.7982534 
cbor             118173   3.188264     1.0       

** Contract: vesting-indices **
Codec            Size    Of minimum   Of maximum
cbor-pure-zlib   4373    1.0          0.27546456
cbor-zlib        4373    1.0          0.27546456
flat-pure-zlib   4566    1.0441345    0.28762203
flat-zlib        4566    1.0441345    0.28762203
flat             7551    1.7267323    0.47565353
cbor             15875   3.630231     1.0       

** Contract: vesting-names **
Codec            Size    Of minimum   Of maximum
flat-pure-zlib   9177    1.0          0.3332849 
flat-zlib        9177    1.0          0.3332849 
cbor-pure-zlib   10524   1.14678      0.38220447
cbor-zlib        10524   1.14678      0.38220447
flat             21928   2.389452     0.79636824
cbor             27535   3.0004358    1.0       
```

