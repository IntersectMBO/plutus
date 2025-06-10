(program 1.0.0
(con string "

Making plutus-tx-plugin work on multiple GHC versions can be painful, because it uses a lot of GHC internals. Since the plugin is not in the dependency closure of the Cardano node, we don’t need to support all the GHC versions, which is helpful. We mostly commit to supporting our primary development version, but we may support other versions as well if it is easy.

The plugin and its dependents should be marked as unbuildable with cabal conditionals on any non-supported major GHC versions. This makes cabal behave reasonably well (it will ignore them and not try and fail to build them).
")
)
