The Plutus Core validation server will behave as follows:

  - Bind to port 3000

  - Accept HTTP requests with a JSON body

  - The server should accept `GET` requests that contain the JSON data for
    validation in the request body

    - For other methods (e.g. `POST`), it will error (response status 400)

  - The server will ignore HTTP headers

  - The server will return response status 200 with no headers. The response
    body will contain JSON: either `True` or `False`
