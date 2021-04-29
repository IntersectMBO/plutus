'use strict';
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
  plugins: [
    require('postcss-import'),
    require('precss'),
    require('tailwindcss'),
    require('autoprefixer'),
    ...extraPlugins
  ]
};
