self: super: {
    rPackages = super.rPackages.override {
        overrides = ({
            hexbin = super.rPackages.hexbin.overrideDerivation(attrs: {
                nativeBuildInputs = attrs.nativeBuildInputs ++ [ super.libiconv ];
                buildInputs = attrs.buildInputs ++ [ super.libiconv ];
            });
        });
    }; 
};
