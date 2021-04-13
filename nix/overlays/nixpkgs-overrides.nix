self: super: {
  z3 = super.callPackage ../pkgs/z3 { };

  morph = super.morph.overrideAttrs (old: {
    # See https://github.com/DBCDK/morph/pull/141
    # Note that this patch does refelct the original content
    # of the PR above since it was broken. 
    patches = [ ../pkgs/morph/sshopts.patch ];
    src = self.fetchFromGitHub {
      owner = "DBCDK";
      repo = "morph";
      rev = "c048d6339f18613a1544bc62ff852cb4c6de1042";
      sha256 = "0yb8prji2nqjsj1aiiqnbqaajbi5l17rg8k78ry7pl3a8sqa3h1x";
    };
  });

}
