# Benchmarking Data for Marlowe Validators

The reference case for benchmarking the Marlowe validators is commit
`ada873544c7dc4ad81f945c3c326b41f0d0862a4` of https://github.com/input-output-hk/marlowe-cardano/.

The folders [semantics/](semantics/) and [rolepayout/](rolepayout/) contain the benchmarking cases
for Marlowe semantics and role-payout validators, respectively. The folder [plutus/](plutus/)
contains their Plutus scripts, serialised in text-envelope format.

The PIR, PLC, and UPLC for the reference validators has been dumped into [flat/](flat/). Here is
the log from when they were generated:

```console
!!! dumping initial PIR program to "./Language.Marlowe.Scripts.pir-initial2432575-0.flat"                                            
!!! dumping simplified PIR program to "./Language.Marlowe.Scripts.pir-simplified2432575-1.flat"                                      
!!! dumping typed PLC program to "./Language.Marlowe.Scripts.plc2432575-2.flat"                                                      
!!! dumping untyped PLC program to "./Language.Marlowe.Scripts.uplc2432575-3.flat"                                                   
!!! dumping initial PIR program to "./Language.Marlowe.Scripts.pir-initial2432575-4.flat"                                            
!!! dumping simplified PIR program to "./Language.Marlowe.Scripts.pir-simplified2432575-5.flat"                                      
!!! dumping typed PLC program to "./Language.Marlowe.Scripts.plc2432575-6.flat"                                                      
!!! dumping untyped PLC program to "./Language.Marlowe.Scripts.uplc2432575-7.flat"                                                   
!!! dumping initial PIR program to "./Language.Marlowe.Scripts.pir-initial2432575-8.flat"                                            
!!! dumping simplified PIR program to "./Language.Marlowe.Scripts.pir-simplified2432575-9.flat"                                      
!!! dumping typed PLC program to "./Language.Marlowe.Scripts.plc2432575-10.flat"                                                     
!!! dumping untyped PLC program to "./Language.Marlowe.Scripts.uplc2432575-11.flat"                                                  
!!! dumping initial PIR program to "./Language.Marlowe.Scripts.pir-initial2432575-12.flat"                                           
!!! dumping simplified PIR program to "./Language.Marlowe.Scripts.pir-simplified2432575-13.flat"                                     
!!! dumping typed PLC program to "./Language.Marlowe.Scripts.plc2432575-14.flat"                                                     
!!! dumping untyped PLC program to "./Language.Marlowe.Scripts.uplc2432575-15.flat"                                                  
!!! dumping initial PIR program to "./Language.Marlowe.Scripts.pir-initial2432575-16.flat"                                           
!!! dumping simplified PIR program to "./Language.Marlowe.Scripts.pir-simplified2432575-17.flat"                                     
!!! dumping typed PLC program to "./Language.Marlowe.Scripts.plc2432575-18.flat"                                                     
!!! dumping untyped PLC program to "./Language.Marlowe.Scripts.uplc2432575-19.flat"                                                  
!!! dumping initial PIR program to "./Language.Marlowe.Scripts.pir-initial2432575-20.flat"                                           
!!! dumping simplified PIR program to "./Language.Marlowe.Scripts.pir-simplified2432575-21.flat"                                     
!!! dumping typed PLC program to "./Language.Marlowe.Scripts.plc2432575-22.flat"                                                     
!!! dumping untyped PLC program to "./Language.Marlowe.Scripts.uplc2432575-23.flat"                                                  
```
