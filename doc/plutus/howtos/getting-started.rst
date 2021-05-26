.. _plutus_getting_started:

How to get started with the Plutus Platform
===========================================

We provide a template repository that you can use to get started quickly.
For now, the only supported tooling setup is to use our provided VSCode devcontainer to get an environment with the correct tools set up.

#. Install Docker using your operating system's package manager (or otherwise).
#. Install VSCode using your operating system's package manager (or otherwise).

    - Install the `Remote Development extension pack <https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.vscode-remote-extensionpack>`_
    - You do *not* need to install the Haskell extension, it will be enabled in the devcontainer. You may want it anyway in case you want to edit files locally.

#. Get the docker image. For now, we need to build this with Nix.

    - Clone `the main Plutus repository <https://github.com/input-output-hk/plutus>`_.
    - Follow the instructions in the ``README`` to set yourself up to build artifacts with Nix (make sure to set up the binary cache!).
    - Build and load the docker container: ``docker load < $(nix-build default.nix -A devcontainer)``.

#. Clone `the template repository <https://github.com/input-output-hk/plutus-starter>`_ and open it in VSCode.

    - It will ask if you want to open it in the container, say yes.

#. Try building the example project from a VSCode terminal using ``cabal build`` .
#. Try opening a Haskell file and experiment with the IDE features (it will take a little while to set up the first time).

Further reading
---------------

This would be a good time to try one of the :ref:`tutorials <plutus_tutorials>`.
