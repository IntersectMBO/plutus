load(
    "@io_tweag_rules_haskell//haskell:haskell.bzl",
    "haskell_import",
    "haskell_library",
)

haskell_packages = [
    "base",
    "directory",
    "filepath",
]

[
    haskell_import(name = name)
    for name in haskell_packages
]

haskell_library(
    name = "runfiles",
    srcs = ["src/Bazel/Runfiles.hs"],
    visibility = ["//visibility:public"],
    deps = [":" + name for name in haskell_packages] + [
    ],
)
