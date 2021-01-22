/*eslint-env node*/
/*global exports global require*/

'use strict';

// Pulling in the image this way plays nicely with Webpack. The
// `plutusLogo` string will actually be the hashed, permalink URL.
// eg. 'e57a929e981d95dd55f1e92be8f3e0bb.png'.
exports.plutusLogo = require('static/images/plutus-logo.svg');
