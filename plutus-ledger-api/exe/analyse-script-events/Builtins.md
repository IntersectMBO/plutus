## Built-in functions involved in mainnet script events

We ran the `count-builtins` analysis (see [README.md](./README.md)) on all
Cardano mainnet script events up to mid-October 2023 (event file beginning
`0000000105908766`; 21,832,781 script events in total).  The results (sorted by
frequency) are shown below.  Builtins unreleased at the time of writing are
omitted because they have not yet been used on the mainnet.

|          Builtin name            |    Total uses   |
|  :-----------------------------  |  -------------: |
|  HeadList                        |    881644746    |
|  IfThenElse                      |    854764718    |
|  TailList                        |    492113114    |
|  EqualsInteger                   |    483469806    |
|  UnConstrData                    |    355025384    |
|  SndPair                         |    325841074    |
|  UnBData                         |    293971343    |
|  FstPair                         |    249617361    |
|  Trace                           |    243130037    |
|  UnIData                         |    221383400    |
|  AddInteger                      |    169915689    |
|  SubtractInteger                 |    120994891    |
|  MultiplyInteger                 |    117192596    |
|  EqualsByteString                |     95913606    |
|  LessThanEqualsInteger           |     79925863    |
|  ChooseList                      |     77389297    |
|  LessThanInteger                 |     65997741    |
|  UnListData                      |     58771072    |
|  DivideInteger                   |     47385959    |
|  UnMapData                       |     40638420    |
|  EqualsData                      |     32820944    |
|  BData                           |     20747611    |
|  MkCons                          |     19690536    |
|  ConstrData                      |     14307826    |
|  IData                           |     13598954    |
|  ChooseData                      |     12980217    |
|  QuotientInteger                 |      9057969    |
|  MkNilData                       |      8665066    |
|  LengthOfByteString              |      8448460    |
|  AppendByteString                |      5350163    |
|  IndexByteString                 |      4549830    |
|  RemainderInteger                |      4300706    |
|  MkPairData                      |      2852806    |
|  NullList                        |      2295654    |
|  ListData                        |      2201376    |
|  ModInteger                      |      1835787    |
|  LessThanEqualsByteString        |      1449792    |
|  LessThanByteString              |      1445947    |
|  SliceByteString                 |      1216642    |
|  MapData                         |      1030125    |
|  Sha3_256                        |       868748    |
|  EqualsString                    |       778767    |
|  ConsByteString                  |       591928    |
|  AppendString                    |       550147    |
|  MkNilPairData                   |       228298    |
|  Sha2_256                        |       197746    |
|  SerialiseData                   |       194855    |
|  ChooseUnit                      |       171916    |
|  VerifyEd25519Signature          |        31974    |
|  EncodeUtf8                      |        13074    |
|  DecodeUtf8                      |        11639    |
|  Blake2b_256                     |         9920    |
|  VerifyEcdsaSecp256k1Signature   |          575    |
|  VerifySchnorrSecp256k1Signature |          575    |
