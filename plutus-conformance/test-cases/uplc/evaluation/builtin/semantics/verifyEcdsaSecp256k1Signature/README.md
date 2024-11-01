### Test vectors for `verifyEcdsaSecp256k1Signature`

Most of the `test-vector-*` test case have been generated using `OpenSSL
3.0.14.4` using the following procedure.

   1. Type `openssl ecparam -name secp256k1 -outform DER -out secp256k1.der` to generate the `secp256k1` elliptic curve parameters and store them in the file `secp256k1.der`
   
   2. Type `openssl ecparam -in secp256k1.der -inform DER -genkey -noout -outform DER -out pk.der`
      to generate a keypair and store it in the file `pk.der`

   3. Type `openssl ec -in pk.der -outform DER -pubout -conv_form compressed -out vk.der` to
      generate a compressed verification key (ie public key) and store it in the file `vk.der`.
   
   4. Given a message in `msg.txt`, generate a signature for the SHA2-256 hash
      of the message using the private key generated earlier using `openssl
      dgst-sha2-256 -sign pk.der msg.txt > sig.txt`.  Use `-sha3-256` instead
      to sign the SHA3-256 hash of the message.  The signature will be stored in
      DER-encoded binary form.  The ECDSA algorithm involves a random number `k`
      which is generated anew for each signature, and each value of `k` produces
      a different signature, so repeating this step will (with very high
      probabilty) generate a different signature every time: all of these are
      valid signatures for the given keypair and message.
      
   5. Look at the contents of `sig.txt` using `dumpasn1 sig.txt`.  This will produce output similar
      to that below.
   
   ```
  0  69: SEQUENCE {
  2  32:   INTEGER
       :     50 F1 64 A7 F6 50 91 4B 3B 7A 25 88 BE 77 54 E5
       :     62 EB 6F 93 E8 31 B9 84 29 69 31 62 8C 86 C5 23
 36  33:   INTEGER
       :     00 9B 5A 92 ED 21 5D 95 82 3E FD 2C 6F A7 10 40
       :     66 DF 0F D3 3D 19 14 EC 9A C8 73 BB 27 D6 2B 11
       :     0E
       :   }
```

   6. The first `INTEGER` entry in the output above is the `r` component of the
      signature, the second is the `s` component.  The two numbers at the start
      of the `INTEGER` lines are the offset of the `INTEGER` object within the
      file and the object's length, which will probably be 32 or 33 for
      Secp256k1.  If the second entry has length 33 (as in this case) the
      signature is a "high s" signature which is accepted by OpenSSL but not by
      `verifyEcdsaSecp256k1Signature` (following
      [Bitcoin](https://github.com/bitcoin/bips/blob/master/bip-0146.mediawiki#low_s);
      see also Section 4.3.3.1 of the Plutus Core specification) .  If this
      happens, discard the signature and generate a new signature until you get
      one whose `s` component has length 32.
      
  7. If the first entry has length 32, concatenate the hex digits with those of the second entry to
     obtain a bytestring of length 64.  If the first entry has length 33, the first byte will be 00.
     Delete this and proceed as in the length 32 case.

  8. Create a Plutus script applying `verifyEcdsaSecp256k1Signature` to
     * A hex string containing the verification key: you can get this by typing 
     `dumpasn1 -20 -p -a vk.der | grep -v BIT | tr -d '\n' | sed 's/ //g' | tr A-Z a-z`.
     * The relevant hash function (`sha2_256` or `sha3_256`) applied to a hex dump of the `msg.txt`
       file, for example obtained by `xxd -p msg.txt`
     * The hex string obtained in Step 7 (this is the signature)
     
  9.  The process can be repeated for the same keypair and message by going back to Step 4, or you
      can start again with a new keypair and/or message.

