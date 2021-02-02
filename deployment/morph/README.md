# Morph Deployments

Morph can be used from any computer with ssh access to the EC2 machines to deploy NixOS configuration.

There is a slight complexity that I haven't yet solved. In order to deploy the machines you need to know their addresses, this information is stored in machines.json which is produced in a temporary directory every time you run the terraform deployment. You need to copy that file into this directory before running `morph deploy ./default.nix switch`.