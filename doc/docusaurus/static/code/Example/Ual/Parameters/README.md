# Data/native parameter verification

Build `docusaurus-examples:exe:example-ual-parameters`. Run PlutusCoreBlaster's
`Tests/BlueprintVerify/run_parameters.py GENERATOR OUTPUT` to generate fresh
blueprint, assurance and checking contexts, check both compiled validators, and
confirm that substituting Data encoding for the native parameter falsifies its
claim without changing the compiled code.

The snapshots contain no historical evidence. Their environment manifest pins a
particular build; regenerate it for your checking environment. Two claims quantify over all integer parameters and raw Data runtime inputs.
Four additional claims check fully applied deployments with parameter seven
(accepted) and eight (rejected), in both Data and native encodings. Their contexts
bind Flat value artifacts, single-CBOR specialized programs and script hashes.
The runner checks nine invalid deployment bindings as well as the original
wire-encoding mutation. These remain bounded evaluation claims; they do not
establish ledger acceptance.
