with {
  lib = rec {
    # copied from nixpkgs
    isDerivation = value: value.type or null == "derivation";

    flattenDepth = depth: x:
      if builtins.isList x && (depth == null || depth >= 0)
      then
        builtins.concatMap
          (flattenDepth (
            if depth != null
            then depth - 1
            else null
          ))
          x
      else [ x ];

    flatten = flattenDepth null;

    collectAttrPaths = predicate: attrs:
      let
        internal = path: attrs:
          let
            inherit
              (builtins.partition
                (attrName: predicate attrs.${attrName})
                (builtins.attrNames attrs))
              right
              wrong
              ;
          in
          map (attrName: path ++ [ attrName ]) right
          ++ (
            if attrs.recurseIntoAttrs or true
            then
              flattenDepth 1
                (
                  map
                    (
                      attrName:
                      internal
                        (path ++ [ attrName ])
                        attrs.${attrName}
                    )
                    (
                      builtins.filter
                        (attrName: builtins.isAttrs attrs.${attrName})
                        wrong
                    )
                )
            else [ ]
          );
      in
      internal [ ] attrs;

    # TODO properly copy `showAttrPath` from nixpkgs
    showAttrPath = builtins.concatStringsSep ".";

    # copied from nixpkgs and simplified
    attrByPath = path: attrs:
      let
        attr = builtins.head path;
      in
      if path == [ ]
      then attrs
      else attrByPath (builtins.tail path) attrs.${attr};
  };
};
flake:
let
  job =
    let
      # mostly a port of `queryMetaStrings()` from the original `hydra-eval-jobs`
      stringProp = attr: subAttr:
        if builtins.isString attr
        then attr
        else if builtins.isList attr
        then
          builtins.concatStringsSep ", "
            (
              builtins.filter
                (value: value != "")
                (
                  map
                    (elem: stringProp elem subAttr)
                    attr
                )
            )
        else if builtins.isAttrs attr
        then toString attr.${subAttr} or ""
        else "";
    in
    drv:
    {
      nixName = drv.name;
      inherit (drv) system drvPath;
      description = drv.meta.description or "";
      license = stringProp drv.meta.license or "" "shortName";
      homepage = drv.meta.homepage or "";
      maintainers = stringProp drv.meta.maintainers or [ ] "email";
      schedulingPriority = drv.meta.schedulingPriority or 100;
      timeout = drv.meta.timeout or 36000;
      maxSilent = drv.meta.maxSilent or 7200;
      isChannel = drv.meta.isHydraChannel or false;
      outputs = builtins.listToAttrs (
        map
          (output: {
            name = output;
            value = drv.${output}.outPath;
          })
          drv.outputs or [ drv.outputName ]
      );
    }
    // (
      if drv._hydraAggregate or false
      then {
        constituents = map (constituent: constituent.drvPath) (
          let
            inherit (builtins.partition builtins.isAttrs drv.constituents) right wrong;
          in
          right ++ map (constituent: result.${constituent}) wrong
        );
      }
      else { }
    );

  result =
    let
      jobAttrs =
        flake.hydraJobs
          or flake.checks
          or (throw "flake does not provide any Hydra jobs or checks");

      jobAttrPaths = lib.collectAttrPaths lib.isDerivation jobAttrs;
    in
    builtins.listToAttrs (
      map
        (path: {
          name = lib.showAttrPath path;
          value = job (lib.attrByPath path jobAttrs);
        })
        jobAttrPaths
    );
in
result
