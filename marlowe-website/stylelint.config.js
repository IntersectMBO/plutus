// This file help us lint the CSS and avoid using the VSCode linter which doesn't work nicely with
// tailwind
// Got this code from: https://stackoverflow.com/questions/61443484/how-to-solve-semi-colon-expected-warnings-css-semicolonexpected
module.exports = {
  extends: ["stylelint-config-standard"],
  rules: {
    "at-rule-no-unknown": [
      true,
      {
        ignoreAtRules: ["tailwind", "apply", "variants", "responsive", "screen"],
      },
    ],
    "declaration-block-trailing-semicolon": null,
    "no-descending-specificity": null,
  },
};
