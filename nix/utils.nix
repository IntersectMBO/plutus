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
}
