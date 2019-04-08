The Plutus Core Validation server exists so that the Rust core nodes can easily
validate Plutus Core.

The Plutus Core validation server will behave as follows:

  - Bind to port 3000

  - Accept HTTP requests with a JSON body

  - The server should accept `GET` requests that contain the JSON data for
    validation in the request body

    - As an example:
      ```json
      {
          "validator": "ab34ce2d",
          "redeemer": "5cb418",
          "data": "958bce"
      }

    - For other methods (e.g. `POST`), it will error (response status 400) and
      return nothing in the response body.

    - If the data is not valid JSON, it will error (response status 400) and
      return nothing in the response body.

  - The server will ignore HTTP headers

  - The server will return response status 200 with no headers. The response
    body will contain JSON: either `True` or `False`

    ```json
    { "isValid": true }
    ```
