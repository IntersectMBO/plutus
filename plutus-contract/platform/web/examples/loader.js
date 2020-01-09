// contract loader
function loadWebPlutusContract(code) {
    return (new Function(code + "\nreturn h$plutusRequestHandler.public;"))();
}

// load a contract locally on node.js
const fs = require('fs');

const source = fs.readFileSync("all.js");
const handler = loadWebPlutusContract(source);
handler.execute( "GET"
               , "/layout"
               , { headers: [], body: "" }
               , x => console.log(x));
