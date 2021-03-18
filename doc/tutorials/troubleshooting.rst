Troubleshooting
===============

Plugin errors
-------------

Errors that start with ``GHC Core to PLC plugin`` are ``plutus-tx-plugin`` errors.
The most common error is:

``Error: Reference to a name which is not a local, a builtin, or an external INLINABLE function``

This means the plugin doesn't have access to implementation of the function, which it needs to be able to compile the function to Plutus Core.
Some things you can do to fix it:

- Make sure to add ``{-# INLINABLE functionname #-}`` to your function.
- If there's an extra ``$c`` in front of the function name in the error, GHC has generated a specialised version of your function,
  which prevents the plugin from accessing it.
  You can turn it off with ``{-# OPTIONS_GHC -fno-specialise #-}``
- Other compiler options that could fix the issue are

  - ``{-# OPTIONS_GHC -fno-strictness #-}``
  - ``{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}``
  - ``{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}``
  - ``{-# OPTIONS_GHC -fobject-code #-}``

  Some more details are in `the plutus-tx readme <https://github.com/input-output-hk/plutus/tree/master/plutus-tx#building-projects-with-plutus-tx>`_.

If you don't need the plugin to succeed, f.e. when Haddock is building documentation,
you can pass the flag ``-fdefer-plugin-errors``.

.. note::
  The recommended way to build documentation is with ``nix-build default.nix -A docs.site``


Haskell language server issues
------------------------------

``ghcide compiled against GHC 8.10.3 but currently using 8.10.2.20201118``

Your editor is not picking up the right version of the haskell language server (HLS).
Plutus needs a custom version of HLS which is provided by Nix. So get this working in your editor, make sure to do these two things:

- Start your editor from ``nix-shell``.
- Most editors are configured to use ``haskell-language-server-wrapper``, which is a wrapper which picks the right HSL version.
  Change this to just ``haskell-language-server``.

If this doesn't work, run ``which haskell-language-server`` in `nix-shell`, and use this absolute path in the configuration of your editor.
