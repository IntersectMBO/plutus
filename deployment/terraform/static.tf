# Static website

resource "aws_s3_bucket" "marlowe_playground" {
  bucket = "marlowe-playground-website-${var.env}"
  acl    = "public-read"

  website {
    index_document = "index.html"
    error_document = "error.html"
  }
}

resource "aws_s3_bucket_policy" "marlowe_playground_website" {
  bucket = aws_s3_bucket.marlowe_playground.id

  policy = <<POLICY
{
    "Version": "2012-10-17",
    "Statement": [
        {
            "Sid": "PublicReadGetObject",
            "Effect": "Allow",
            "Principal": "*",
            "Action": [
                "s3:GetObject"
            ],
            "Resource": [
                "arn:aws:s3:::marlowe-playground-website-${var.env}/*"
            ]
        }
    ]
}
POLICY
}

resource "aws_iam_role" "s3_proxy_role" {
  name               = "marlowe_website_s3_${var.env}"
  path               = "/"  
  assume_role_policy = <<EOF
{
  "Version": "2012-10-17",
  "Statement": [
    {
      "Action": "sts:AssumeRole",
      "Principal": {
        "Service": "apigateway.amazonaws.com"
      },
      "Effect": "Allow",
      "Sid": ""
    }
  ]
}
EOF
}

# Root path
resource "aws_api_gateway_method" "marlowe_root_get_method" {
  rest_api_id      = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  resource_id      = aws_api_gateway_rest_api.marlowe_symbolic_lambda.root_resource_id
  http_method      = "GET"
  authorization    = "NONE"
  api_key_required = false
}

resource "aws_api_gateway_integration" "marlowe_root_get_method" {
  rest_api_id      = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  resource_id      = aws_api_gateway_rest_api.marlowe_symbolic_lambda.root_resource_id
  http_method      = aws_api_gateway_method.marlowe_root_get_method.http_method

  type                    = "AWS"
  integration_http_method = "GET"
  credentials             = "${aws_iam_role.s3_proxy_role.arn}"
  uri                     = "arn:aws:apigateway:${var.aws_region}:s3:path/marlowe-playground-website-${var.env}/index.html"
}

resource "aws_api_gateway_method_response" "marlowe_root_get_method" {
  rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  resource_id      = aws_api_gateway_rest_api.marlowe_symbolic_lambda.root_resource_id
  http_method = aws_api_gateway_method.marlowe_root_get_method.http_method
  status_code = "200"

  response_parameters = {
    "method.response.header.Access-Control-Allow-Headers" = true
    "method.response.header.Access-Control-Allow-Methods" = true
    "method.response.header.Access-Control-Allow-Origin"  = true
    "method.response.header.Content-Type" = true
  }

  depends_on = [aws_api_gateway_method.marlowe_root_get_method]
}

resource "aws_api_gateway_integration_response" "marlowe_root_get_method" {
  rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  resource_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.root_resource_id
  http_method = aws_api_gateway_method.marlowe_root_get_method.http_method

  status_code = aws_api_gateway_method_response.marlowe_root_get_method.status_code

  response_parameters = {
    "method.response.header.Access-Control-Allow-Origin" = "'*'"
    "method.response.header.Content-Type" = "integration.response.header.Content-Type"
  }
}

# Other static files
resource "aws_api_gateway_resource" "website_item_resource" {
  rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  parent_id   = aws_api_gateway_rest_api.marlowe_symbolic_lambda.root_resource_id
  path_part   = "{item}"
}

resource "aws_api_gateway_method" "marlowe_item_get_method" {
  rest_api_id      = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  resource_id      = aws_api_gateway_resource.website_item_resource.id
  http_method      = "GET"
  authorization    = "NONE"
  api_key_required = false

  request_parameters = {
    "method.request.path.item"   = true
  }
}

resource "aws_api_gateway_integration" "marlowe_item_get_method" {
  rest_api_id      = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  resource_id      = aws_api_gateway_resource.website_item_resource.id
  http_method = aws_api_gateway_method.marlowe_item_get_method.http_method

  type                    = "AWS"
  integration_http_method = "GET"
  credentials             = "${aws_iam_role.s3_proxy_role.arn}"
  uri                     = "arn:aws:apigateway:${var.aws_region}:s3:path/marlowe-playground-website-${var.env}/{item}"

  request_parameters = {
    "integration.request.path.item"   = "method.request.path.item"
  }
}

resource "aws_api_gateway_method_response" "marlowe_item_get_method" {
  rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  resource_id = aws_api_gateway_resource.website_item_resource.id
  http_method = aws_api_gateway_method.marlowe_item_get_method.http_method
  status_code = "200"

  response_parameters = {
    "method.response.header.Access-Control-Allow-Headers" = true
    "method.response.header.Access-Control-Allow-Methods" = true
    "method.response.header.Access-Control-Allow-Origin"  = true
    "method.response.header.Content-Type" = true
  }

  depends_on = [aws_api_gateway_method.marlowe_item_get_method]
}

resource "aws_api_gateway_integration_response" "marlowe_item_get_method" {
  rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  resource_id = aws_api_gateway_resource.website_item_resource.id
  http_method = aws_api_gateway_method.marlowe_item_get_method.http_method

  status_code = aws_api_gateway_method_response.marlowe_item_get_method.status_code

  response_parameters = {
    "method.response.header.Access-Control-Allow-Origin" = "'*'"
    "method.response.header.Content-Type" = "integration.response.header.Content-Type"
  }
}
