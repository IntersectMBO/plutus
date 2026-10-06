# Data/native parameter verification

Build `docusaurus-examples:exe:example-ual-parameters`. Run PlutusCoreBlaster's
`Tests/BlueprintVerify/run_parameters.py GENERATOR OUTPUT` to generate fresh
blueprint, assurance and checking contexts, check both compiled validators, and
confirm that substituting Data encoding for the native parameter falsifies its
claim without changing the compiled code.

The snapshots contain no historical evidence. Their environment manifest pins a
particular build; regenerate it for your checking environment. Both claims quantify
over all integer parameters and raw Data runtime inputs. These are bounded
execution claims, not ledger acceptance or deployment checks.
