{ fetchurl, fetchgit, linkFarm, runCommandNoCC, gnutar }: rec {
  offline_cache = linkFarm "offline" packages;
  packages = [
    {
      name = "chartist_plugin_axistitle___chartist_plugin_axistitle_0.0.4.tgz";
      path = fetchurl {
        name = "chartist_plugin_axistitle___chartist_plugin_axistitle_0.0.4.tgz";
        url = "https://registry.yarnpkg.com/chartist-plugin-axistitle/-/chartist-plugin-axistitle-0.0.4.tgz";
        sha1 = "102d7b84260061292dff666b918fedc955deb144";
      };
    }
    {
      name = "chartist_plugin_tooltips___chartist_plugin_tooltips_0.0.17.tgz";
      path = fetchurl {
        name = "chartist_plugin_tooltips___chartist_plugin_tooltips_0.0.17.tgz";
        url = "https://registry.yarnpkg.com/chartist-plugin-tooltips/-/chartist-plugin-tooltips-0.0.17.tgz";
        sha1 = "fc1a98eb5d3771235b6e08cd1c18cc96c2110660";
      };
    }
    {
      name = "chartist___chartist_0.11.4.tgz";
      path = fetchurl {
        name = "chartist___chartist_0.11.4.tgz";
        url = "https://registry.yarnpkg.com/chartist/-/chartist-0.11.4.tgz";
        sha1 = "e96e1c573d8b67478920a3a6ae52359d9fc8d8b7";
      };
    }
  ];
}
