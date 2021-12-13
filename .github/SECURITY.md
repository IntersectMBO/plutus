# Security policy
 
## Scope

Please only report an issue here if it relates specifically to the Plutus Core language or compiler.
This is also an appropriate place to report issues that stem from the EUTXO ledger model.

Note that many security issues will instead appear in specific applications or in the [libraries that support them](https://github.com/input-output-hk/plutus-apps). 

## Weaknesses

If you have found a _weakness_ (in the sense of the [CWE](https://cwe.mitre.org/); a source of potential vulnerabilities) that affects users of this library, please open a "Security report" issue and describe it as a weakness.
If you believe that public disclosure of the weakness would be irresponsible (e.g. because it would lead to quick discovery of vulnerabilities in existing applications), then please instead email security@iohk.io.

A typical example of a weakness might be "if you use the function F you might assume that it has property P, but under conditions C it does not, which could lead to exploitable behaviour".
This is a weakness, since it highlights a general source of issues that may or may not be present in any given application depending on how it is designed.

## Vulnerabilities

If you have a found a _vulnerability_ (in the sense of the [CVE](https://www.cve.org/); a weakeness in a particular piece of software that allows it to be exploited), please do _not_ open an issue, and instead contact security@iohk.io.

A typical example of a vulnerability might be "due to a bug, the function F does not check that a transaction has been signed with a particular key, despite the documentation saying that it does".
This is a vulnerability, since it leads to directly exploitable behaviour in any application that uses the function in question.
