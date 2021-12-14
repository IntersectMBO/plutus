{ system
  , compiler
  , flags
  , pkgs
  , hsPkgs
  , pkgconfPkgs
  , errorHandler
  , config
  , ... }:
  {
    flags = {
      support_aesni = true;
      support_rdrand = true;
      support_pclmuldq = false;
      support_sse = false;
      integer-gmp = true;
      support_deepseq = true;
      old_toolchain_inliner = false;
      check_alignment = false;
      use_target_attributes = true;
      };
    package = {
      specVersion = "1.18";
      identifier = { name = "cryptonite"; version = "0.29"; };
      license = "BSD-3-Clause";
      copyright = "Vincent Hanquez <vincent@snarc.org>";
      maintainer = "vincent@snarc.org";
      author = "Vincent Hanquez <vincent@snarc.org>";
      homepage = "https://github.com/haskell-crypto/cryptonite";
      url = "";
      synopsis = "Cryptography Primitives sink";
      description = "A repository of cryptographic primitives.\n\n* Symmetric ciphers: AES, DES, 3DES, CAST5, Blowfish, Twofish, Camellia, RC4, Salsa, XSalsa, ChaCha.\n\n* Hash: SHA1, SHA2, SHA3, SHAKE, MD2, MD4, MD5, Keccak, Skein, Ripemd, Tiger, Whirlpool, Blake2\n\n* MAC: HMAC, KMAC, Poly1305\n\n* Asymmetric crypto: DSA, RSA, DH, ECDH, ECDSA, ECC, Curve25519, Curve448, Ed25519, Ed448\n\n* Key Derivation Function: PBKDF2, Scrypt, HKDF, Argon2, BCrypt, BCryptPBKDF\n\n* Cryptographic Random generation: System Entropy, Deterministic Random Generator\n\n* Data related: Anti-Forensic Information Splitter (AFIS)\n\nIf anything cryptographic related is missing from here, submit\na pull request to have it added. This package strives to be a\ncryptographic kitchen sink that provides cryptography for everyone.\n\nEvaluate the security related to your requirements before using.\n\nRead \"Crypto.Tutorial\" for a quick start guide.";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = ".";
      dataFiles = [];
      extraSrcFiles = [
        "cbits/*.h"
        "cbits/aes/*.h"
        "cbits/ed25519/*.h"
        "cbits/decaf/include/*.h"
        "cbits/decaf/include/decaf/*.h"
        "cbits/decaf/include/arch_32/*.h"
        "cbits/decaf/include/arch_ref64/*.h"
        "cbits/decaf/p448/arch_32/*.h"
        "cbits/decaf/p448/arch_ref64/*.h"
        "cbits/decaf/p448/*.h"
        "cbits/decaf/ed448goldilocks/decaf_tables.c"
        "cbits/decaf/ed448goldilocks/decaf.c"
        "cbits/include32/p256/*.h"
        "cbits/include64/p256/*.h"
        "cbits/blake2/ref/*.h"
        "cbits/blake2/sse/*.h"
        "cbits/argon2/*.h"
        "cbits/argon2/*.c"
        "cbits/aes/x86ni_impl.c"
        "cbits/cryptonite_hash_prefix.c"
        "tests/*.hs"
        ];
      extraTmpFiles = [];
      extraDocFiles = [ "README.md" "CHANGELOG.md" ];
      };
    components = {
      "library" = {
        depends = ((([
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
          (hsPkgs."basement" or (errorHandler.buildDepError "basement"))
          (hsPkgs."ghc-prim" or (errorHandler.buildDepError "ghc-prim"))
          ] ++ (pkgs.lib).optional (!(compiler.isGhc && (compiler.version).lt "8.0")) (hsPkgs."base" or (errorHandler.buildDepError "base"))) ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."Win32" or (errorHandler.buildDepError "Win32"))) ++ (pkgs.lib).optional (compiler.isGhc && true && flags.integer-gmp) (hsPkgs."integer-gmp" or (errorHandler.buildDepError "integer-gmp"))) ++ (pkgs.lib).optional (flags.support_deepseq) (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"));
        libs = (pkgs.lib).optional (system.isLinux) (pkgs."pthread" or (errorHandler.sysDepError "pthread")) ++ (pkgs.lib).optional (system.isWindows) (pkgs."advapi32" or (errorHandler.sysDepError "advapi32"));
        buildable = if compiler.isGhc && (compiler.version).lt "8.0"
          then false
          else true;
        modules = ([
          "Crypto/Cipher/AES/Primitive"
          "Crypto/Cipher/Blowfish/Box"
          "Crypto/Cipher/Blowfish/Primitive"
          "Crypto/Cipher/CAST5/Primitive"
          "Crypto/Cipher/Camellia/Primitive"
          "Crypto/Cipher/DES/Primitive"
          "Crypto/Cipher/Twofish/Primitive"
          "Crypto/Cipher/Types/AEAD"
          "Crypto/Cipher/Types/Base"
          "Crypto/Cipher/Types/Block"
          "Crypto/Cipher/Types/GF"
          "Crypto/Cipher/Types/Stream"
          "Crypto/Cipher/Types/Utils"
          "Crypto/Error/Types"
          "Crypto/Number/Compat"
          "Crypto/Hash/Types"
          "Crypto/Hash/Blake2"
          "Crypto/Hash/Blake2s"
          "Crypto/Hash/Blake2sp"
          "Crypto/Hash/Blake2b"
          "Crypto/Hash/Blake2bp"
          "Crypto/Hash/SHA1"
          "Crypto/Hash/SHA224"
          "Crypto/Hash/SHA256"
          "Crypto/Hash/SHA384"
          "Crypto/Hash/SHA512"
          "Crypto/Hash/SHA512t"
          "Crypto/Hash/SHA3"
          "Crypto/Hash/SHAKE"
          "Crypto/Hash/Keccak"
          "Crypto/Hash/MD2"
          "Crypto/Hash/MD4"
          "Crypto/Hash/MD5"
          "Crypto/Hash/RIPEMD160"
          "Crypto/Hash/Skein256"
          "Crypto/Hash/Skein512"
          "Crypto/Hash/Tiger"
          "Crypto/Hash/Whirlpool"
          "Crypto/Random/Entropy/Source"
          "Crypto/Random/Entropy/Backend"
          "Crypto/Random/ChaChaDRG"
          "Crypto/Random/SystemDRG"
          "Crypto/Random/Probabilistic"
          "Crypto/PubKey/Internal"
          "Crypto/PubKey/ElGamal"
          "Crypto/ECC/Simple/Types"
          "Crypto/ECC/Simple/Prim"
          "Crypto/Internal/Builder"
          "Crypto/Internal/ByteArray"
          "Crypto/Internal/Compat"
          "Crypto/Internal/CompatPrim"
          "Crypto/Internal/DeepSeq"
          "Crypto/Internal/Imports"
          "Crypto/Internal/Nat"
          "Crypto/Internal/Words"
          "Crypto/Internal/WordArray"
          "Crypto/Cipher/AES"
          "Crypto/Cipher/AESGCMSIV"
          "Crypto/Cipher/Blowfish"
          "Crypto/Cipher/CAST5"
          "Crypto/Cipher/Camellia"
          "Crypto/Cipher/ChaCha"
          "Crypto/Cipher/ChaChaPoly1305"
          "Crypto/Cipher/DES"
          "Crypto/Cipher/RC4"
          "Crypto/Cipher/Salsa"
          "Crypto/Cipher/TripleDES"
          "Crypto/Cipher/Twofish"
          "Crypto/Cipher/Types"
          "Crypto/Cipher/Utils"
          "Crypto/Cipher/XSalsa"
          "Crypto/ConstructHash/MiyaguchiPreneel"
          "Crypto/Data/AFIS"
          "Crypto/Data/Padding"
          "Crypto/ECC"
          "Crypto/ECC/Edwards25519"
          "Crypto/Error"
          "Crypto/MAC/CMAC"
          "Crypto/MAC/Poly1305"
          "Crypto/MAC/HMAC"
          "Crypto/MAC/KMAC"
          "Crypto/Number/Basic"
          "Crypto/Number/F2m"
          "Crypto/Number/Generate"
          "Crypto/Number/ModArithmetic"
          "Crypto/Number/Nat"
          "Crypto/Number/Prime"
          "Crypto/Number/Serialize"
          "Crypto/Number/Serialize/LE"
          "Crypto/Number/Serialize/Internal"
          "Crypto/Number/Serialize/Internal/LE"
          "Crypto/KDF/Argon2"
          "Crypto/KDF/PBKDF2"
          "Crypto/KDF/Scrypt"
          "Crypto/KDF/BCrypt"
          "Crypto/KDF/BCryptPBKDF"
          "Crypto/KDF/HKDF"
          "Crypto/Hash"
          "Crypto/Hash/IO"
          "Crypto/Hash/Algorithms"
          "Crypto/OTP"
          "Crypto/PubKey/Curve25519"
          "Crypto/PubKey/Curve448"
          "Crypto/PubKey/MaskGenFunction"
          "Crypto/PubKey/DH"
          "Crypto/PubKey/DSA"
          "Crypto/PubKey/ECC/Generate"
          "Crypto/PubKey/ECC/Prim"
          "Crypto/PubKey/ECC/DH"
          "Crypto/PubKey/ECC/ECDSA"
          "Crypto/PubKey/ECC/P256"
          "Crypto/PubKey/ECC/Types"
          "Crypto/PubKey/ECDSA"
          "Crypto/PubKey/ECIES"
          "Crypto/PubKey/Ed25519"
          "Crypto/PubKey/Ed448"
          "Crypto/PubKey/EdDSA"
          "Crypto/PubKey/RSA"
          "Crypto/PubKey/RSA/PKCS15"
          "Crypto/PubKey/RSA/Prim"
          "Crypto/PubKey/RSA/PSS"
          "Crypto/PubKey/RSA/OAEP"
          "Crypto/PubKey/RSA/Types"
          "Crypto/PubKey/Rabin/OAEP"
          "Crypto/PubKey/Rabin/Basic"
          "Crypto/PubKey/Rabin/Modified"
          "Crypto/PubKey/Rabin/RW"
          "Crypto/PubKey/Rabin/Types"
          "Crypto/Random"
          "Crypto/Random/Types"
          "Crypto/Random/Entropy"
          "Crypto/Random/EntropyPool"
          "Crypto/Random/Entropy/Unsafe"
          "Crypto/System/CPU"
          "Crypto/Tutorial"
          ] ++ (pkgs.lib).optional (flags.support_rdrand && (system.isI386 || system.isX86_64) && !system.isWindows) "Crypto/Random/Entropy/RDRand") ++ (if system.isWindows
          then [ "Crypto/Random/Entropy/Windows" ]
          else [ "Crypto/Random/Entropy/Unix" ]);
        cSources = (((([
          "cbits/cryptonite_chacha.c"
          "cbits/cryptonite_salsa.c"
          "cbits/cryptonite_xsalsa.c"
          "cbits/cryptonite_rc4.c"
          "cbits/cryptonite_cpu.c"
          "cbits/p256/p256.c"
          "cbits/p256/p256_ec.c"
          "cbits/cryptonite_blake2s.c"
          "cbits/cryptonite_blake2sp.c"
          "cbits/cryptonite_blake2b.c"
          "cbits/cryptonite_blake2bp.c"
          "cbits/cryptonite_poly1305.c"
          "cbits/cryptonite_sha1.c"
          "cbits/cryptonite_sha256.c"
          "cbits/cryptonite_sha512.c"
          "cbits/cryptonite_sha3.c"
          "cbits/cryptonite_md2.c"
          "cbits/cryptonite_md4.c"
          "cbits/cryptonite_md5.c"
          "cbits/cryptonite_ripemd.c"
          "cbits/cryptonite_skein256.c"
          "cbits/cryptonite_skein512.c"
          "cbits/cryptonite_tiger.c"
          "cbits/cryptonite_whirlpool.c"
          "cbits/cryptonite_scrypt.c"
          "cbits/cryptonite_pbkdf2.c"
          "cbits/ed25519/ed25519.c"
          "cbits/argon2/argon2.c"
          ] ++ (if system.isX86_64 || system.isAarch64
          then [
            "cbits/decaf/p448/arch_ref64/f_impl.c"
            "cbits/decaf/p448/f_generic.c"
            "cbits/decaf/p448/f_arithmetic.c"
            "cbits/decaf/utils.c"
            "cbits/decaf/ed448goldilocks/scalar.c"
            "cbits/decaf/ed448goldilocks/decaf_all.c"
            "cbits/decaf/ed448goldilocks/eddsa.c"
            ]
          else [
            "cbits/decaf/p448/arch_32/f_impl.c"
            "cbits/decaf/p448/f_generic.c"
            "cbits/decaf/p448/f_arithmetic.c"
            "cbits/decaf/utils.c"
            "cbits/decaf/ed448goldilocks/scalar.c"
            "cbits/decaf/ed448goldilocks/decaf_all.c"
            "cbits/decaf/ed448goldilocks/eddsa.c"
            ])) ++ (if system.isX86_64 || system.isAarch64
          then [ "cbits/curve25519/curve25519-donna-c64.c" ]
          else [
            "cbits/curve25519/curve25519-donna.c"
            ])) ++ (pkgs.lib).optional (flags.support_rdrand && (system.isI386 || system.isX86_64) && !system.isWindows) "cbits/cryptonite_rdrand.c") ++ (if flags.support_aesni && (system.isLinux || system.isFreebsd || system.isOsx) && (system.isI386 || system.isX86_64)
          then [
            "cbits/aes/x86ni.c"
            "cbits/aes/generic.c"
            "cbits/aes/gf.c"
            "cbits/cryptonite_aes.c"
            ]
          else [
            "cbits/aes/generic.c"
            "cbits/aes/gf.c"
            "cbits/cryptonite_aes.c"
            ])) ++ (if system.isX86_64 || flags.support_sse
          then [
            "cbits/blake2/sse/blake2s.c"
            "cbits/blake2/sse/blake2sp.c"
            "cbits/blake2/sse/blake2b.c"
            "cbits/blake2/sse/blake2bp.c"
            ]
          else [
            "cbits/blake2/ref/blake2s-ref.c"
            "cbits/blake2/ref/blake2sp-ref.c"
            "cbits/blake2/ref/blake2b-ref.c"
            "cbits/blake2/ref/blake2bp-ref.c"
            ]);
        jsSources = (pkgs.lib).optional (system.isGhcjs) "jsbits/cryptonite.js";
        includeDirs = (([
          "cbits"
          "cbits/ed25519"
          "cbits/decaf/include"
          "cbits/decaf/p448"
          "cbits/argon2"
          ] ++ (if system.isX86_64 || system.isAarch64
          then [ "cbits/include64" ]
          else [
            "cbits/include32"
            ])) ++ (if system.isX86_64 || system.isAarch64
          then [
            "cbits/decaf/include/arch_ref64"
            "cbits/decaf/p448/arch_ref64"
            ]
          else [
            "cbits/decaf/include/arch_32"
            "cbits/decaf/p448/arch_32"
            ])) ++ (if system.isX86_64 || flags.support_sse
          then [ "cbits/blake2/sse" ]
          else [ "cbits/blake2/ref" ]);
        };
      tests = {
        "test-cryptonite" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
            (hsPkgs."tasty-hunit" or (errorHandler.buildDepError "tasty-hunit"))
            (hsPkgs."tasty-kat" or (errorHandler.buildDepError "tasty-kat"))
            (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
            ];
          buildable = true;
          modules = [
            "BlockCipher"
            "ChaCha"
            "BCrypt"
            "BCryptPBKDF"
            "ECC"
            "ECC/Edwards25519"
            "ECDSA"
            "Hash"
            "Imports"
            "KAT_AES/KATCBC"
            "KAT_AES/KATECB"
            "KAT_AES/KATGCM"
            "KAT_AES/KATCCM"
            "KAT_AES/KATOCB3"
            "KAT_AES/KATXTS"
            "KAT_AES"
            "KAT_AESGCMSIV"
            "KAT_AFIS"
            "KAT_Argon2"
            "KAT_Blowfish"
            "KAT_CAST5"
            "KAT_Camellia"
            "KAT_Curve25519"
            "KAT_Curve448"
            "KAT_DES"
            "KAT_Ed25519"
            "KAT_Ed448"
            "KAT_EdDSA"
            "KAT_CMAC"
            "KAT_HKDF"
            "KAT_HMAC"
            "KAT_KMAC"
            "KAT_MiyaguchiPreneel"
            "KAT_PBKDF2"
            "KAT_OTP"
            "KAT_PubKey/DSA"
            "KAT_PubKey/ECC"
            "KAT_PubKey/ECDSA"
            "KAT_PubKey/OAEP"
            "KAT_PubKey/PSS"
            "KAT_PubKey/P256"
            "KAT_PubKey/RSA"
            "KAT_PubKey/Rabin"
            "KAT_PubKey"
            "KAT_RC4"
            "KAT_Scrypt"
            "KAT_TripleDES"
            "KAT_Twofish"
            "ChaChaPoly1305"
            "Number"
            "Number/F2m"
            "Padding"
            "Poly1305"
            "Salsa"
            "Utils"
            "XSalsa"
            ];
          hsSourceDirs = [ "tests" ];
          mainPath = [ "Tests.hs" ];
          };
        };
      benchmarks = {
        "bench-cryptonite" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
            (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
            (hsPkgs."gauge" or (errorHandler.buildDepError "gauge"))
            (hsPkgs."random" or (errorHandler.buildDepError "random"))
            (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
            ];
          buildable = true;
          modules = [ "Number/F2m" ];
          hsSourceDirs = [ "benchs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../contrib/cryptonite-0.29; }