{ lib }:

rec {

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

  date_YYYYMMDDHHmmSS_ToIso8601 = ts:
    let
      year = lib.substring 0 4 ts;
      month = lib.substring 4 2 ts;
      day = lib.substring 6 2 ts;
      hour = lib.substring 8 2 ts;
      minute = lib.substring 10 2 ts;
      second = lib.substring 12 2 ts;
    in
    "${year}-${month}-${day}T${hour}:${minute}:${second}Z";
}
