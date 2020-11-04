## API Gateway

resource "aws_api_gateway_rest_api" "marlowe" {
  name        = "marlowe_${var.env}"
  description = "API Gateway for the Marlowe Playground"
  endpoint_configuration {
    types = ["REGIONAL"]
  }
  binary_media_types = ["image/x-icon", "font/woff2", "font/ttf"]
}

resource "aws_api_gateway_usage_plan" "marlowe" {
  name = "marlowe_${var.env}"

  api_stages {
    api_id = aws_api_gateway_rest_api.marlowe.id
    stage  = aws_api_gateway_deployment.marlowe.stage_name
  }

  quota_settings {
    limit  = 86400
    offset = 0
    period = "DAY"
  }
}

resource "aws_api_gateway_deployment" "marlowe" {
  depends_on = [
    aws_api_gateway_integration.marlowe_root_get_method,
    aws_api_gateway_integration.marlowe_item_get_method,
    aws_api_gateway_integration.marlowe_playground_lambda,
    aws_api_gateway_integration.marlowe_symbolic,
    aws_api_gateway_integration.marlowe_runghc,
  ]

  rest_api_id = aws_api_gateway_rest_api.marlowe.id
  stage_name  = var.env
}

resource "aws_api_gateway_domain_name" "marlowe" {
  domain_name = local.marlowe_domain_name

  regional_certificate_arn   = data.aws_acm_certificate.marlowe_private.arn
  endpoint_configuration {
    types = ["REGIONAL"]
  }
}

resource "aws_api_gateway_base_path_mapping" "marlowe" {
  # The path, if not specified, is `/` by default
  api_id      = aws_api_gateway_rest_api.marlowe.id
  stage_name  = aws_api_gateway_deployment.marlowe.stage_name
  domain_name = aws_api_gateway_domain_name.marlowe.domain_name
}

# Static Site
## Root item
resource "aws_api_gateway_method" "marlowe_root_get_method" {
  rest_api_id      = aws_api_gateway_rest_api.marlowe.id
  resource_id      = aws_api_gateway_rest_api.marlowe.root_resource_id
  http_method      = "GET"
  authorization    = "NONE"
  api_key_required = false
}

resource "aws_api_gateway_integration" "marlowe_root_get_method" {
  rest_api_id      = aws_api_gateway_rest_api.marlowe.id
  resource_id      = aws_api_gateway_rest_api.marlowe.root_resource_id
  http_method      = aws_api_gateway_method.marlowe_root_get_method.http_method

  type                    = "AWS"
  integration_http_method = "GET"
  credentials             = aws_iam_role.marlowe_s3_proxy_role.arn
  uri                     = "arn:aws:apigateway:${var.aws_region}:s3:path/marlowe-playground-website-${var.env}/index.html"
}

resource "aws_api_gateway_method_response" "marlowe_root_get_method" {
  rest_api_id = aws_api_gateway_rest_api.marlowe.id
  resource_id      = aws_api_gateway_rest_api.marlowe.root_resource_id
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
  rest_api_id = aws_api_gateway_rest_api.marlowe.id
  resource_id = aws_api_gateway_rest_api.marlowe.root_resource_id
  http_method = aws_api_gateway_method.marlowe_root_get_method.http_method

  status_code = aws_api_gateway_method_response.marlowe_root_get_method.status_code

  response_parameters = {
    "method.response.header.Access-Control-Allow-Origin" = "'*'"
    "method.response.header.Content-Type" = "integration.response.header.Content-Type"
  }

  depends_on = [
    aws_api_gateway_integration.marlowe_root_get_method
  ]
}

## Other static files
resource "aws_api_gateway_resource" "marlowe_website_item_resource" {
  rest_api_id = aws_api_gateway_rest_api.marlowe.id
  parent_id   = aws_api_gateway_rest_api.marlowe.root_resource_id
  path_part   = "{proxy+}"
}

resource "aws_api_gateway_method" "marlowe_item_get_method" {
  rest_api_id      = aws_api_gateway_rest_api.marlowe.id
  resource_id      = aws_api_gateway_resource.marlowe_website_item_resource.id
  http_method      = "GET"
  authorization    = "NONE"

  request_parameters = {
    "method.request.path.proxy"   = true
  }
}

resource "aws_api_gateway_integration" "marlowe_item_get_method" {
  rest_api_id      = aws_api_gateway_rest_api.marlowe.id
  resource_id      = aws_api_gateway_resource.marlowe_website_item_resource.id
  http_method = aws_api_gateway_method.marlowe_item_get_method.http_method

  type                    = "HTTP_PROXY"
  integration_http_method = "GET"
  credentials             = aws_iam_role.marlowe_s3_proxy_role.arn
  uri                     = "https://${aws_s3_bucket.marlowe_playground.bucket_regional_domain_name}/{proxy}"

  request_parameters = {
    "integration.request.path.proxy"   = "method.request.path.proxy"
  }
}

resource "aws_api_gateway_method_response" "marlowe_item_get_method" {
  rest_api_id = aws_api_gateway_rest_api.marlowe.id
  resource_id = aws_api_gateway_resource.marlowe_website_item_resource.id
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
  rest_api_id = aws_api_gateway_rest_api.marlowe.id
  resource_id = aws_api_gateway_resource.marlowe_website_item_resource.id
  http_method = aws_api_gateway_method.marlowe_item_get_method.http_method

  status_code = aws_api_gateway_method_response.marlowe_item_get_method.status_code

  response_parameters = {
    "method.response.header.Access-Control-Allow-Origin" = "'*'"
    "method.response.header.Content-Type" = "integration.response.header.Content-Type"
  }
}


# Marlowe Playground API
resource "aws_api_gateway_resource" "marlowe_api" {
   rest_api_id = aws_api_gateway_rest_api.marlowe.id
   parent_id   = aws_api_gateway_rest_api.marlowe.root_resource_id
   path_part   = "api"
}

resource "aws_api_gateway_resource" "marlowe_playground_lambda" {
  depends_on = [
    aws_api_gateway_resource.marlowe_api,
  ]
   rest_api_id = aws_api_gateway_rest_api.marlowe.id
   parent_id   = aws_api_gateway_resource.marlowe_api.id
   path_part   = "{proxy+}"
}

resource "aws_api_gateway_method" "marlowe_playground_lambda" {
   rest_api_id   = aws_api_gateway_rest_api.marlowe.id
   resource_id   = aws_api_gateway_resource.marlowe_playground_lambda.id
   http_method   = "ANY"
   authorization = "NONE"
}

resource "aws_api_gateway_integration" "marlowe_playground_lambda" {
  rest_api_id = aws_api_gateway_rest_api.marlowe.id
  resource_id = aws_api_gateway_method.marlowe_playground_lambda.resource_id
  http_method = aws_api_gateway_method.marlowe_playground_lambda.http_method

  integration_http_method = "POST"
  type                    = "AWS_PROXY"
  uri                     = aws_lambda_function.marlowe_playground.invoke_arn

  request_parameters = {
  }
}

resource "aws_lambda_permission" "marlowe_playground_lambda_api_gw" {
  statement_id  = "AllowAPIGatewayInvoke"
  action        = "lambda:InvokeFunction"
  function_name = aws_lambda_function.marlowe_playground.function_name
  principal     = "apigateway.amazonaws.com"

  # The "/*/*" portion grants access from any method on any resource
  # within the API Gateway REST API.
  source_arn = "${aws_api_gateway_rest_api.marlowe.execution_arn}/*/*"
}

# Marlowe Symbolic
resource "aws_api_gateway_resource" "marlowe_symbolic" {
  rest_api_id = aws_api_gateway_rest_api.marlowe.id
  parent_id   = aws_api_gateway_rest_api.marlowe.root_resource_id
  path_part   = "marlowe-analysis"
}

resource "aws_api_gateway_method" "marlowe_symbolic" {
  rest_api_id   = aws_api_gateway_rest_api.marlowe.id
  resource_id   = aws_api_gateway_resource.marlowe_symbolic.id
  http_method   = "POST"
  authorization = "NONE"
  api_key_required = false
}

resource "aws_api_gateway_integration" "marlowe_symbolic" {
  rest_api_id = aws_api_gateway_rest_api.marlowe.id
  resource_id = aws_api_gateway_method.marlowe_symbolic.resource_id
  http_method = aws_api_gateway_method.marlowe_symbolic.http_method

  integration_http_method = "POST"
  type                    = "AWS_PROXY"
  uri                     = aws_lambda_function.marlowe_symbolic.invoke_arn

  request_parameters = {
  }
}

resource "aws_lambda_permission" "marlowe_symbolic_lambda_api_gw" {
  statement_id  = "AllowAPIGatewayInvoke"
  action        = "lambda:InvokeFunction"
  function_name = aws_lambda_function.marlowe_symbolic.function_name
  principal     = "apigateway.amazonaws.com"

  # The "/*/*" portion grants access from any method on any resource
  # within the API Gateway REST API.
  source_arn = "${aws_api_gateway_rest_api.marlowe.execution_arn}/*/*"
}

# runghc proxy
resource "aws_api_gateway_resource" "marlowe_runghc" {
  depends_on = [
  ]
   rest_api_id = aws_api_gateway_rest_api.marlowe.id
   parent_id   = aws_api_gateway_rest_api.marlowe.root_resource_id
   path_part   = "runghc"
}

resource "aws_api_gateway_method" "marlowe_runghc" {
   rest_api_id   = aws_api_gateway_rest_api.marlowe.id
   resource_id   = aws_api_gateway_resource.marlowe_runghc.id
   http_method   = "POST"
   authorization = "NONE"
}

resource "aws_api_gateway_integration" "marlowe_runghc" {
  rest_api_id = aws_api_gateway_rest_api.marlowe.id
  resource_id = aws_api_gateway_method.marlowe_runghc.resource_id
  http_method = aws_api_gateway_method.marlowe_runghc.http_method

  integration_http_method = "POST"
  type                    = "HTTP_PROXY"
  uri                     = "http://${aws_alb.plutus.dns_name}/runghc"

  request_parameters = {
  }
}

# Route 53
resource "aws_route53_record" "marlowe_api_gw" {
  name    = local.marlowe_domain_name
  type    = "A"
  zone_id = var.marlowe_public_zone
  alias {
    name                   = aws_api_gateway_domain_name.marlowe.regional_domain_name
    zone_id                = aws_api_gateway_domain_name.marlowe.regional_zone_id
    evaluate_target_health = true
  }
}
