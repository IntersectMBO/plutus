-- the header of public key should be 02 or 03
-- 04 is for uncompressed, we don't have uncompressed
-- other bits would also break, e.g. 01,05...
(program 0.0.0 [[[(builtin verifyEcdsaSecp256k1Signature)
 (con bytestring #04e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01)]
 (con bytestring #e253af0766804b869bb1595be9765b534886bbaab8305bf50dbc7f899bfb5f01)]
 (con bytestring #b2fc46ad47af464478c199e1f8be169f1be6327c7f9a0a6689371ca94caf04064a01b22aff1520abd58951341603faed768cf78ce97ae7b038abfe456aa17c09)])