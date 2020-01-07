## 3. Merklising Programs

### Introduction

This document carries on from the previous notes on [Merklised
Abstract Syntax Trees](./Merklisation-notes.md) and looks at the
effects of Merklising programs.

The document mentioned above and the one examining
[erasure](Erasure.md) of types and other information from Plutus Core
ASTs both contain statistics for validation code from the sample
contracts in
[`plutus-use-cases`](https://github.com/input-output-hk/plutus/tree/master/plutus-use-cases).
However, those documents deal with unapplied validators, which are
just functions.  To study the full potential of Merklisation we
require executable validators, which are obtained by applying
validators to suitable arguments (a redeemer, a data value, and a
`PendingTx` object containing information about the transaction being
validated).  Once these arguments have been supplied a it become
possible to run a validator, and when it is run some parts of the AST
(depending on the arguments) may not be required and can safely be
Merklised away, reducing the size of the on-chain validation code.

It can be quite difficult to construct suitable inputs, but
fortunately `plutus-use-cases` contains a comprehensive set of tests
which execute sample contracts on the mockchain.  There are generally
a number of tests for each contract, exercising different behaviours
of the contract.  By modifying the testing code slightly I was able to
insert code to carry out Merklisation experiments on applied
validators.

### Methodology

To perform Merklisation based on execution paths, I used a modified
version of the CEK machine which executes a Plutus Core program and
records which AST nodes are evaluated; a subsequent phase traverses
the AST and uses this information to replace unused nodes with their
Merkle hashes (using a new AST node type called `Prune` which contains
the hash of the deleted subtree).

### Validator sizes

The sizes of the validators that we'll see later differ from the sizes
seen in other documents.  There are two reason for this:

   * The size of the applied validator includes the sizes of its arguments, 
     and these can be quite large. For the sample contracts the sizes are 
     typically as follows:
      * Data value:  2200-2400 nodes, 27-30 kilobytes in serialised form
      * Redeemer: similar to the data value
      * `PendingTx`: 2800-36000 nodes, 36-46 kilobytes 
   * Even before validation, the size of the validator changes, so caution 
     is required when comparing the results reported here with results in 
     other documents.   For example, the off-chain validator for the Game 
     example has 13273 nodes and is 90960 bytes long when serialised, but 
     the on-chain validator has 13779 nodes and is 99973 bytes long (and 
     some other contracts have much bigger discrepancies).  There are (at least) 
     three reasons for the difference:
      * For the purposes of the earlier experiments I exported validator code from 
        each contract.  The exported validator code wasn't always exactly the same 
        as the validator in the contract (sometimes parameters are required to construct 
        the actual validator which aren't statically available in the contract).
      * The validator has to be extended to include extra code, for example for 
        decoding `Data` objects.
      * Types are normalised in on-chain code.  It looks as if this typically 
        _reduces_ the size of the code, mainly because type instantiations are 
        removed (type variables are replaced with actual types in the bodies of abstractions).

### Results

I modified the `plutus-use-cases` test to analyse all of the
validators.  Some of the analysis involved "minimising" the
validators, by which I mean applying the transformations in the
second-last column of the table in the [type erasure document](./Erasure.md): 
removing all kinds, types, and type-related
information from the AST; removing all textual names; and replacing
unique identifiers in names with De Bruijn indices.  The serialised
versions still included unit annotations, so could be made slightly
smaller.

The information collected (and summarised in the table below) was as follows:

  * The number of term nodes in the applied validator
  * The number of term nodes actually used
  * The number of bytes in the serialised version of the unaltered validator
  * The number of bytes in the serialised minimised version of the validator
  * The number of bytes in the serialised Merklised validator. 
    Three different strategies for Merklisation of types were used:
      * All types were replaced by Merkle hashes
      * Types were only replaced by Merkle hashes if their serialised versions took up more than 32 bytes
      * Types were left unchanged, with no type-level Merkle hashes
      * Another strategy would have been to intern types in a separate table 
        (probably included in PLC `Program` objects), but this would have 
        required major changes to the Plutus codebase, so I didn't attempt to do it.
  * Finally, the Merklised version of the validator was minimised and serialised, 
    and the size measured (the type-Merklisation strategy doesn't affect this number, 
    since all types are discarded during minimisation).

The table also contains figures showing the sizes of the various
versions of the validators after serialisation and compression (using
gzip with maximum compression).

Certain validators reappeared numerous times during the tests, so I've
removed duplicates.  The compressed sizes of identically-sized
validators sometimes varied by a few bytes (presumably because
differences in identically sized pieces of data within the validators
would make the serialised version slightly more or less compressible),
so I've removed those as well.  Note that for a given use-case,
validators with significantly different sizes may appear: this is
because multiple different types of transaction can occur during a
test and these have different validators (for example, the
Crowdfunding example performs transactions which collect from and pay
to scripts in addition to the main validator).

Here are the results (if the table's too wide for the page you can click on
it and use the left and right arrow keys to scroll it horizontally).

| Term nodes | Used nodes | Unmerklised, serialised | Unmerklised, minimised, serialised | All types Merklised | Big types Merklised | No types Merklised | Merklised, minimised |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---:  |
|  **Crowdfunding** | | | | | | | |
| 10539| 7297 | 307807 | 24444 | 175130 | 140947 | 219398 | 31721 | 
|      | Compressed: | 40592 | 4519 | 68520 | 54805 | 42577 | 14980 |
| 10248 | 5438 | 303010 | 23523 | 138620 | 111870 | 179984 | 27986 | 
|      | Compressed: | 40386 | 4350 | 54163 | 44821 | 36082 | 14903 |
| 10539 | 7297 | 307807 | 24444 | 175130 | 140947 | 219398 | 31721 | 
|      | Compressed: | 40592 | 4519 | 68520 | 54805 | 42577 | 14980 |
|  **Currency** | | | | | | | |
| 8615| 6888 | 254083 | 20145 | 157259 | 124385 | 192758 | 28415 | 
|      | Compressed: | 31519 | 3778 | 56046 | 44702 | 34728 | 12562 |
| 6282 | 4487 | 203384 | 15079 | 111008 | 90258 | 142785 | 22593 | 
|      | Compressed: | 23113 | 3128 | 37339 | 30790 | 25867 | 11327 |
|  **Escrow** | | | | | | | |
| 11102| 6816 | 316769 | 25961 | 165305 | 134033 | 213226 | 30450 | 
|      | Compressed: | 40753 | 4867 | 64765 | 52572 | 41140 | 15008 |
| 11328 | 7048 | 320492 | 26632 | 169148 | 137843 | 216952 | 31101 | 
|      | Compressed: | 40830 | 4919 | 64813 | 52623 | 41230 | 15028 |
| 10876 | 5225 | 313046 | 25290 | 133998 | 108641 | 177588 | 27431 | 
|      | Compressed: | 40561 | 4735 | 52052 | 43533 | 35253 | 14913 |
|  **Future** | | | | | | | |
| 8615| 6888 | 254047 | 20109 | 157223 | 124349 | 192722 | 28379 | 
|      | Compressed: | 31494 | 3763 | 56030 | 44683 | 34706 | 12543 |
| 6282 | 4487 | 203360 | 15055 | 110984 | 90234 | 142761 | 22569 | 
|      | Compressed: | 23097 | 3118 | 37324 | 30777 | 25851 | 11313 |
| 11526 | 7485 | 323963 | 27315 | 178434 | 145728 | 226496 | 32798 | 
|      | Compressed: | 41068 | 5048 | 66016 | 53774 | 42597 | 15601 |
| 11453 | 7412 | 322794 | 27107 | 177239 | 144533 | 225327 | 32590 | 
|      | Compressed: | 41054 | 5042 | 66005 | 53764 | 42595 | 15595 |
| 16839 | 9516 | 423404 | 39821 | 231972 | 190042 | 308449 | 42634 | 
|      | Compressed: | 55891 | 7000 | 88244 | 71923 | 57339 | 21164 |
| 16472 | 8939 | 417425 | 38936 | 220702 | 180393 | 300006 | 40155 | 
|      | Compressed: | 55859 | 6953 | 86185 | 70198 | 55708 | 20111 |
|      | Compressed: | 55851 | 6946 | 86183 | 70194 | 55703 | 20107 |
|  **Game** | | | | | | | |
| 5396| 3843 | 190850 | 12708 | 98439 | 79382 | 128427 | 20678 | 
|      | Compressed: | 21369 | 2814 | 33947 | 28108 | 23575 | 10895 |
| 5396 | 3848 | 190850 | 12708 | 98541 | 79406 | 128451 | 20652 | 
|      | Compressed: | 21369 | 2812 | 34003 | 28127 | 23593 | 10897 |
|  **Game state machine** | | | | | | | |
| 12174| 6763 | 316653 | 28951 | 167208 | 134955 | 216000 | 31648 | 
|      | Compressed: | 41371 | 5083 | 64101 | 52073 | 41563 | 16032 |
| 12416 | 8131 | 320652 | 29624 | 195061 | 157358 | 249763 | 34669 | 
|      | Compressed: | 41518 | 5209 | 72191 | 57942 | 46130 | 16193 |
| 12709 | 8431 | 325444 | 30428 | 199974 | 162238 | 254533 | 35421 | 
|      | Compressed: | 41615 | 5277 | 72230 | 57986 | 46164 | 16197 |
| 12416 | 5870 | 320651 | 29623 | 146844 | 120052 | 199578 | 29880 | 
|      | Compressed: | 41520 | 5209 | 52349 | 43665 | 37753 | 15631 |
|  **Multisig** | | | | | | | |
| 6472| 4724 | 208797 | 15534 | 116175 | 92682 | 148619 | 23059 | 
|      | Compressed: | 25027 | 3417 | 41331 | 33573 | 27388 | 11590 |
| 6496 | 4677 | 209252 | 15688 | 115574 | 92541 | 148470 | 23283 | 
|      | Compressed: | 25142 | 3496 | 41131 | 33639 | 27667 | 11826 |
|  **Multisig state machine** | | | | | | | |
| 16787| 9130 | 403721 | 39660 | 224930 | 181296 | 291423 | 41606 | 
|      | Compressed: | 55584 | 7096 | 87637 | 70558 | 56403 | 20674 |
| 16809 | 9600 | 404135 | 39775 | 233918 | 187531 | 292849 | 43502 | 
|      | Compressed: | 55660 | 7105 | 90700 | 72965 | 57630 | 21409 |
| 16823 | 9631 | 404397 | 39875 | 234429 | 187955 | 293269 | 43612 | 
|      | Compressed: | 55626 | 7114 | 90695 | 72960 | 57622 | 21398 |
| 16837 | 9645 | 404659 | 39975 | 234695 | 188221 | 293531 | 43712 | 
|      | Compressed: | 55711 | 7116 | 90705 | 72966 | 57667 | 21402 |
| 16811 | 9814 | 404176 | 39815 | 236739 | 190290 | 295266 | 42857 | 
|      | Compressed: | 55633 | 7110 | 93771 | 75268 | 58906 | 21049 |
| 16804 | 6755 | 404045 | 39765 | 170978 | 139101 | 226863 | 35188 | 
|      | Compressed: | 55630 | 7113 | 66437 | 55175 | 46374 | 19083 |
| 16636 | 8638 | 401297 | 39327 | 211481 | 171100 | 272917 | 38728 | 
|      | Compressed: | 55554 | 7056 | 85620 | 69217 | 53768 | 19373 |
|  **Pubkey** | | | | | | | |
| 5994| 4199 | 198673 | 14187 | 106193 | 85443 | 138074 | 21701 | 
|      | Compressed: | 22942 | 3002 | 37186 | 30637 | 25204 | 11211 |
|  **Token account** | | | | | | | |
| 8556| 6785 | 253227 | 19976 | 155710 | 123150 | 191524 | 28368 | 
|      | Compressed: | 31486 | 3754 | 55991 | 44741 | 34815 | 12714 |
| 6234 | 4439 | 202646 | 14945 | 110254 | 89504 | 142047 | 22459 | 
|      | Compressed: | 23087 | 3111 | 37317 | 30768 | 25844 | 11307 |
| 8142 | 6371 | 267998 | 18555 | 152109 | 123325 | 196041 | 27671 | 
|      | Compressed: | 34332 | 3412 | 59361 | 47704 | 36842 | 13173 |
|  **Vesting** | | | | | | | |
| 10666 | 7680 | 314175 | 24437 | 183161 | 146899 | 230861 | 31956 | 
|      | Compressed: | 41427 | 4384 | 71787 | 57129 | 43523 | 14834 |
| 10548 | 7426 | 312217 | 24074 | 178471 | 143053 | 226803 | 31214 | 
|      | Compressed: | 41396 | 4359 | 71205 | 56677 | 42645 | 14658 |

### Remarks

The results of Merklisation are rather disappointing.  For example, in
the first line of the table we see that the validator has 10539 term
nodes and only 7297 of those are used during evaluation. This suggests
that Merklising away the unused nodes would save about 30% for the
term nodes alone, with additional savings from type nodes.  This is
indeed the case: the original AST serialises to 307807 bytes and the
Merklised versions serialise to 175130, 140947, and 219398 bytes
(depending on the type-Merklisation strategy); however the Merklised
versions are much less compressible: the unaltered validator
compresses to 40592 bytes, but the compressed sizes of the Merklised
ones are all larger: 68520, 54805, and 42577 bytes.

The difference is even more noticeable for the minimised versions: if
we minimise the original validator and then compress it we get
something 4519 bytes long (less than 1.5% of the size of the
uncompressed unminimised validator), but if we Merklise, minimise, and
then compress then we get something 14980 bytes long.  This is
presumably because the hashes introduced by Merklisation are highly
incompressible, which might be expected on information-theoretic
grounds.  The Merklised validator in this case contains 418 hashes in
term nodes, each occupying 32 bytes.  In total this is 13376 bytes,
which is of the same order of magnitude as the difference between the
compressed versions of the Merklised and un-Merklised validators
(10461 bytes).

These patterns are repeated throughout the results.  Every Merklised
validator contains 300-600 hashed terms (these numbers aren't shown in
the table), and probably because of this the compressed versions of
the minimised Merklised validators are uniformly on the order of 10K
larger than the un-Merklised versions.  If you look at the figures for
the Merklised versions, the compressed sizes vary inversely with the
uncompressed sizes, even when we try to be careful about not
Merklising small types.  The earlier suggestion of interning types
might solve this problem, although I didn't try that because it would
have required quite a lot of work.


### Update: being more careful about what we Merklise

It wasn't initially clear why Merklisation seems to be ineffective in
the table above, but closer inspection of the data showed that a large
number of small terms were being Merklised. For example, for the first
entry in the table (the Crowdfunding validator), 418 AST nodes were
being Merklised, but 286 of these had 10 or fewer subnodes and only 31
had 70 or more subnodes.  In an effort to avoid Merklisation of small
terms I added a threshold to the Merklisation process so that only
nodes whose serialised form was greater than the threshold would be
Merklised.  The table below shows the effect of varying this
threshold. I've only included figures for the first entry from the
earlier table, but the behaviour appears to be similar for the other
examples.  Merklised AST nodes serialise to 36 bytes, so there's a
special entry for that threshold in the table.  For completeness the
table still contains data for different type-Merklisation strategies,
but it's probably best to look at the last two columns: "No types
Merklised", where the variations are purely due to term Merklisation
and "Merklised, minimised", where terms are Merklised but types are
discarded and names are replaced with De Bruijn indices with no
extraneous data.

Recall that the validator contained 10539 term nodes, of which only
7297 were used in that particular run.  When serialised the
um-Merklised validator takes up 307807 bytes, compressing to 40592;
when minimised and serialised it takes up 24444 bytes, compressing to
4519.


| Merklisation Threshold | Merklised nodes | All types Merklised |  Big types Merklised |  No types Merklised | Merklised, minimised | 
| ---: | ---: | ---: | ---: | ---: |---: |
| 0       | 418 | 175130 | 140947 | 219398 | 31721 | 
| | (compressed) |  68520 | 54805 | 42577 | 14980 |
| 36      | 319  | 173560 | 139377 | 217828 | 28660 | 
| | (compressed) | 66374 | 52629 | 40202 | 12416 |
| 50      | 244  | 174022 | 139839 | 218290 | 26328 | 
| | (compressed) | 65658 | 51844 | 39340 | 11567 |
| 100     | 123  | 177865 | 143682 | 222133 | 22927 | 
| | (compressed) | 62611 | 48595 | 35826 | 7759 |
| 150     | 81   | 181310 | 147127 | 225578 | 21929 | 
| | (compressed) | 62081 | 47965 | 35057 | 6431 |
| 200     | 64   | 183586 | 149403 | 227854 | 21755 | 
| | (compressed) | 62120 | 47928 | 34901 | 5908 |
| 250     | 50   | 186070 | 151887 | 230338 | 21564 | 
| | (compressed) | 62290 | 48014 | 34947 | 5592 |
| 300     | 45   | 187206 | 153023 | 231474 | 21613 | 
| | (compressed) | 62380 | 48027 | 34955 | 5449 |
| 350     | 42   | 188115 | 153932 | 232383 | 21684 | 
| | (compressed) | 62446 | 48043 | 34939 | 5381 |
| 400     | 36   | 190208 | 156025 | 234476 | 21827 | 
| | (compressed) | 62719 | 48234 | 35038 | 5236 |
| 450     | 35   | 190612 | 156429 | 234880 | 21897 | 
| | (compressed) | 62810 | 48306 | 35081 | 5222 |
| 500     | 33   |  191488 | 157305 | 235756 | 22016 | 
| | (compressed) | 62922 | 48407 | 35175 | 5189 |

As you'd expect, the smallest serialised sizes occur when the
Merklisation threshold is 36, the point at which the serialised forms
of Merklised terms are the same size as their un-Merklised versions;
however, after that point (fewer terms Merklised) serialised sizes
increase but compressed sizes _decrease_.  I suspect that this is
because different terms often have similar subterms (except perhaps
for identifiers in names) and that this is favourable for compression.
When terms are Merklised, any differences change the hash completely
and reduces compressibility.

Note also that that though introducing a threshold for Merklisation
improves its effectiveness, it also introduces a lot of extra
computation into the procedure for calculating Merkle hashes.  For
every node that we may need to Merklise we have to serialise it first
and see how big the result is before deciding whether to proceed with
Merklisation, which is already expensive.


## Overall conclusions

Merklisation doesn't seem to be very effective for Plutus Core.  On
the other hand, we can save a lot of space by removing extraneous
information from ASTs and then compressing their serialised forms.

Type information takes up a great deal of space in Plutus Core ASTs
(typically of the order of 70% of the serialised AST), but we might be
able to mitigate this by interning types in a separate table; with the
exception of discarding types altogether, other strategies were not 
very effective.