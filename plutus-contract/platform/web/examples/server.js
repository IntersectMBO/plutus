/*
  This example creates a 'network' contract from a 'web' contract.
 */

// contract loader
function loadWebPlutusContract(code) {
    return (new Function(code + "\nreturn h$plutusRequestHandler.public;"))();
}

const fs = require('fs');
const http = require('http');

const contractFileName = 'all.js'
const envName = 'PLUTUS_CONTRACT_HTTP_PORT';

// find the port to listen
function getListenPort() {
  function getNum(str) {
    return ( typeof str === 'string' && str.match(/^[0-9]+$/))
           ? parseInt(str)
           : -1;
  }

  // command line
  if(process.argv.length === 3) {
    let num = getNum(process.argv[2]);
    if(num !== -1) return num;
  }

  // environment
  let num = getNum(process.env[envName]);
  if(num !== -1) return num;

  // default
  return 16523; // 408B

}

const contractCode = fs.readFileSync(contractFileName);
const contract = loadWebPlutusContract(contractCode);

const server = http.createServer((req, res) => {
  // consume the request body
  let data = [];
  req.on('data', chunk => { data.push(chunk) });
  req.on('end', () => {
    // convert the request headers
    let h, headers = [];
    for(h in req.headers) {
      headers.push([h, req.headers[h]]);
    }
    // convert the request to an ArrayBuffer
    let bb   = Buffer.concat(data)
    let body = bb.buffer.slice(bb.byteOffset, bb.byteOffset + bb.length);
    let options = { headers: headers
                  , body: body
                  }
    contract.execute(req.method, req.url, options, result => {
      // convert the response and call the callback
      res.statusCode = result.status;
      result.headers.forEach(hdr => res.setHeader(hdr[0], hdr[1]));
      res.end(Buffer.from(result.body));
    });
  });
});

server.on('clientError', (err, socket) => {
  socket.end('HTTP/1.1 400 Bad Request\r\n\r\n');
});

// output our listen address the same way as the "network" flavour
const port = getListenPort();
console.log(envName + ":" + port);
server.listen(port);
