{ lib }:
{
  flattenDerivationTree = separator: set:
    let
      recurse = name: name':
        flatten (if name == "" then name' else "${name}${separator}${name'}");

      flatten = name: value:
        if lib.isDerivation value || lib.typeOf value != "set" then
          [{ inherit name value; }]
        else
          lib.concatLists (lib.mapAttrsToList (recurse name) value);

    in
    assert lib.typeOf set == "set"; lib.listToAttrs (flatten "" set);


  makeHydraRequiredJob = { self, pkgs }:
    let
      clean-jobs =
        lib.filterAttrsRecursive (name: _: name != "recurseForDerivations")
          (removeAttrs self.hydraJobs.${pkgs.system} [ "required" ]);
    in
    pkgs.releaseTools.aggregate {
      name = "required";
      meta.description = "All jobs required to pass CI";
      constituents = lib.collect lib.isDerivation clean-jobs;
    };
}
