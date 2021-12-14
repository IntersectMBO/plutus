// this is here to help link cryptonite calls into cardano-crypto.
// this is all so terrible...
mergeInto(LibraryManager.library, {
    cryptonite_chacha_combine : function(...args) { return h$cryptonite._cryptonite_chacha_combine(...args); },
    cryptonite_chacha_init : function(...args) { return h$cryptonite._cryptonite_chacha_init(...args); },
    cryptonite_fastpbkdf2_hmac_sha512 : function(...args) { return h$cryptonite._cryptonite_fastpbkdf2_hmac_sha512(...args); },
    cryptonite_sha512_finalize : function(...args) { return h$cryptonite._cryptonite_sha512_finalize(...args); },
    cryptonite_sha512_init : function(...args) { return h$cryptonite._cryptonite_sha512_init(...args); },
    cryptonite_sha512_update : function(...args) { return h$cryptonite._cryptonite_sha512_update(...args); }
});