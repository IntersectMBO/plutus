# Plutus Example Project

## Get Started

Two methods for developing Plutus applications are provided here:

1. Developing with Nix using a `nix-shell`
2. Developing with Docker and VSCode dev containers

The `nix-shell` environment has all the necessary tools configured for building
Plutus applications. If you already have Nix installed, or a Haskell editor you
prefer, you may enjoy this method.

The Docker/VSCode environment builds a full-featured Haskell/Plutus development environment
based on Docker and VSCode. It requires only Docker and VSCode to be installed, and uses Haskell IDE
Engine inside the container to provide a Haskell IDE. Those less familiar with Nix 
may prefer this method.

### Developing with Nix

This folder contains a `shell.nix` file that builds a configured development
environment for Plutus projects. With [Nix installed](https://nixos.org/nix/manual/#chap-installation),
you can follow these steps to enter the environment for this example project:

#### 1. Clone the Plutus repository and copy this example project

```
$ git clone https://github.com/input-output-hk/plutus.git
$ cp -r ./plutus/example <path to your project>
$ cd <path to your project>
```

#### 2. Enter the nix-shell

```
$ nix-shell
```

The `nix-shell` command will examine the `shell.nix` file of this folder, and create
an isolated environment where the packages and tools defined in that file are available.

Once the `nix-shell` environment has loaded, you can edit your project files
with any Haskell editor you prefer, then in the `nix-shell` you can build your project with 
`cabal v2-build` or compile and run your project's executable with `cabal v2-run example-exe`.

### Developing with Docker and VSCode

The University of Wyoming's IOHK Blockchain Research and Development Lab
maintains [Docker images for development on the Plutus Platform](https://hub.docker.com/repository/docker/uwyoiohk/plutus-development).
Those images can be used as [VSCode dev containers](https://code.visualstudio.com/docs/remote/containers)
to make a full-featured Plutus development environment.

The images contain GHC with a configured Haskell IDE Engine installation that
works out-of-the-box for Plutus development.

##### Prerequisites:

1. [Install Docker](https://docs.docker.com/get-docker/)
2. [Install Visual Studio Code](https://code.visualstudio.com/)
3. [Install the Remote Development Extension Pack for Visual Studio Code](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.vscode-remote-extensionpack)

After you've completed the prerequisites, follow the steps below:

#### 1. Clone the Plutus repository and copy this example project

```
$ git clone https://github.com/input-output-hk/plutus.git
$ cp -r ./plutus/example <path to your project>
$ cd <path to your project>
```

#### 2. Open VSCode in your project folder

If you've installed VSCode correctly and put it's CLI on your `PATH`,
this can be done by running:

```
$ code <path to your project>
```

Or you can just open your project from inside VSCode.

#### 3. Open your project in a container

With the [Remote Development Extension Pack](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.vscode-remote-extensionpack)
installed in VSCode, you will see a green button at the bottom left corner of
the window:

![Remote development button](https://i.imgur.com/LfIEZsB.png)

Click that button, and select the "Remote-Containers: Reopen in Container"
option:

![Reopen in Container](https://i.imgur.com/k1ELZel.jpg)

This will reload your VSCode window, and place you inside a workspace folder (`/plutus`) in
the container that is [bind mounted](https://docs.docker.com/storage/bind-mounts/)
to your project's folder.

Once inside the dev container, you can build your project with `cabal v2-build`
or compile and run your project's executable with `cabal v2-run example-exe`. You can
also stop/restart/remove the container whenever.
