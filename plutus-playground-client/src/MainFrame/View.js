/*eslint-env node*/
/*global exports global require*/

'use strict';

// Pulling in the image this way plays nicely with Webpack. The `plutusLogo` string will
// actually be the hashed, permalink URL. eg. 'e57a929e981d95dd55f1e92be8f3e0bb.png'.
// Note: `global.plutusLogo` is not defined in `src/entry.js`, but _is_ defined in
// `test/Main.js`. This ensures that the tests pass, even though the test suite
// cannot resolve the path to the image.
exports.plutusLogo = global.plutusLogo || require('static/images/plutus-logo.svg');
