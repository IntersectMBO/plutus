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
  parser: 'postcss-scss',
  plugins: [
    require("postcss-import"),
    require('postcss-nested'),
    // require("tailwindcss"),
    require("autoprefixer"),
    ...extraPlugins
  ]
};
