"use strict";
const extraPlugins =
  process.env.NODE_ENV === "production"
    ? [
        require("cssnano")({
          preset: [
            "default",
            {
              discardComments: {
                removeAll: true,
              },
            },
          ],
        }),
      ]
    : [];

module.exports = {
  // FIXME: Try to remove nesting in the redesign and remove `postcss-scss` and `postcss-nested`
  parser: 'postcss-scss',
  plugins: [
    require("postcss-import"),
    require('postcss-nested'),
    require("tailwindcss"),
    require("autoprefixer"),
    ...extraPlugins
  ]
};
