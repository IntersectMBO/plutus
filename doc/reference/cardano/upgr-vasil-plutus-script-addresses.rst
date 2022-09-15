.. _upgrading_to_vasil_and_plutus_script_addresses:

Upgrading to Vasil and Plutus script addresses
====================================================

A Plutus V2 script will not have the same hash value as a Plutus V1 script
----------------------------------------------------------------------------------

DApp developers might expect that when doing a migration from ``PlutusV1`` scripts 
to ``PlutusV2`` scripts, the same source code, when recompiled, will generate the 
same hash value of that script address. However, it is impossible for a compiled 
``PlutusV2`` script to have the same script hash and address as a compiled ``PlutusV1`` script. 

Using the exact same script with different language versions will result in different 
hashes. The exact same script (as in ``UPLC.Program``) can be used as a ``PlutusV1`` script 
or a ``PlutusV2`` script, and since the language version is part of the hash, the two 
hashes will be different. 

A Plutus V1 script will not necessarily have the same hash value when recompiled with a later version of the Plutus Compiler
----------------------------------------------------------------------------------------------------------------------------------

Suppose you write your Haskell source code (Plutus Tx), compile it into Plutus Core 
code (PLC), generate its hash value, then use it in a transaction. If you don’t save 
your compiled code, and then decide to use the same script in the future, you would 
have to recompile it. This could result in a different hash value of the script address 
even without upgrading from ``PlutusV1`` to ``PlutusV2`` scripts. This is because the hash 
is computed based on the output of the compiled code. 

Given Plutus compiler version changes, changes in the dependencies, and multiple 
other improvements, it is expected that the hash value of the script address will 
change after the source code is recompiled. 

When to export and save the output of a compiled script
---------------------------------------------------------------------

Once you expect that you will not modify the on-chain part of your application and 
you don’t want the hash value of your script address to change, the best way to 
keep it the same is to save the output of your final compiled Plutus Core code (PLC) 
to a file. 

For details on how to export scripts, please see :doc:`How to export scripts, datums and 
redeemers </howtos/exporting-a-script>`. 
