import { themes as prismThemes } from "prism-react-renderer";
import type { Config } from "@docusaurus/types";
import type * as Preset from "@docusaurus/preset-classic";

const config: Config = {
  title: "Plinth and Plutus Core Documentation",
  tagline: "Plinth and Plutus Core user guide",
  favicon: "img/favicon.ico",

  // Set the production url of your site here
  url: process.env.DOCUSAURUS_URL || "https://plutus.cardano.intersectmbo.org",

  // Set the /<baseUrl>/ pathname under which your site is served
  // For GitHub pages deployment, it is often '/<projectName>/'
  baseUrl: process.env.DOCUSAURUS_BASE_URL || "/docs/",

  // GitHub pages deployment config.
  // If you aren't using GitHub pages, you don't need these.
  organizationName: "facebook", // Usually your GitHub org/user name.
  projectName: "docusaurus", // Usually your repo name.

  onBrokenLinks: "throw",
  onBrokenAnchors: "throw",
  onBrokenMarkdownLinks: "throw",
  trailingSlash: false,

  plugins: [
    [
      require.resolve("@cmfcmf/docusaurus-search-local"),
      {
        indexDocs: true
      }
    ],
    [
      "@docusaurus/plugin-google-gtag",
      {
        trackingID: "G-X6364ZT8L2",
        anonymizeIP: true
      }
    ]
  ],

  // Even if you don't use internationalization, you can use this field to set
  // useful metadata like html lang. For example, if your site is Chinese, you
  // may want to replace "en" with "zh-Hans".
  i18n: {
    defaultLocale: "en",
    locales: ["en"]
  },
  markdown: {
    mermaid: true
  },
  themes: ["@docusaurus/theme-mermaid"],

  presets: [
    [
      "classic",
      {
        docs: {
          routeBasePath: "/",
          sidebarPath: "./sidebars.ts",
          // Please change this to your repo.
          // Remove this to remove the "edit this page" links.
          editUrl:
            "https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus"
        },
        theme: {
          customCss: "./src/css/custom.css"
        }
      } satisfies Preset.Options
    ]
  ],

  themeConfig: {
    // Replace with your project's social card
    image: "img/docusaurus-social-card.png",
    navbar: {
      title: "Plutus",
      logo: {
        alt: "Plutus Logo",
        src: "img/logo.svg",
        srcDark: "img/logo-white.svg"
      },
      items: [
        {
          type: "docSidebar",
          sidebarId: "tutorialSidebar",
          position: "left",
          label: "User guide"
        },
        {
          type: "html",
          position: "right",
          value:
            '<a href="https://github.com/IntersectMBO/plutus" class="github-link" target="_blank"></a>'
        }
      ]
    },
    footer: {
      style: "dark",
      links: [],
      copyright: `Copyright`
    },
    prism: {
      theme: prismThemes.github,
      darkTheme: prismThemes.dracula,
      additionalLanguages: ["haskell"]
    }
  } satisfies Preset.ThemeConfig
};

export default config;
