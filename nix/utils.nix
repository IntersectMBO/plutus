{ lib }:

rec {

  # Flattens a nested attribute set of derivations into name/value pairs.
  # Used in: `nix/outputs.nix` (to build `flattened-ci-jobs` and `ciJobs`).
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


  # Aggregates CI jobs which are required for Hydra to pass.
  # Used in: `nix/outputs.nix` (to compute `hydra-required-job`).
  makeHydraRequiredJob = { self, pkgs }:
    let
      clean-jobs =
        lib.filterAttrsRecursive (name: _: name != "recurseForDerivations")
          (removeAttrs self.hydraJobs.${pkgs.stdenv.hostPlatform.system} [ "required" ]);
    in
    pkgs.releaseTools.aggregate {
      name = "required";
      meta.description = "All jobs required to pass CI";
      constituents = lib.collect lib.isDerivation clean-jobs;
    };


  # Retrieves the git revision from flake sourceInfo, or "unknown".
  # Used in: `nix/project.nix` (adds `__GIT_REV__` CPP macro to builds).
  # When the git tree is dirty, the sourceInfo attribute is missing from inputs.self.
  getSourceInfoRev = inputs:
    if inputs.self.sourceInfo ? rev then
      inputs.self.sourceInfo.rev
    else
      "unknown";


  # Converts flake sourceInfo lastModifiedDate to ISO-8601, or empty string.
  # Used in: `nix/project.nix` (adds `__GIT_COMMIT_DATE__` CPP macro).
  # When the git tree is dirty, the sourceInfo attribute is missing from inputs.self.
  getSourceInfoLastModifiedDate = inputs:
    if inputs.self.sourceInfo ? lastModifiedDate then
      date_YYYYMMDDHHmmSS_ToIso8601 inputs.self.sourceInfo.lastModifiedDate
    else
      "";


  # Helper to convert YYYYMMDDHHmmSS timestamps to ISO-8601.
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
