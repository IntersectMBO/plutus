-- From  https://github.com/HachiSecurity/plc-llvm/tree/main/compiler/test-data/untyped
(program 1.0.0
    [(lam x (force [(lam y y) x])) (delay (con integer 4))]
)
