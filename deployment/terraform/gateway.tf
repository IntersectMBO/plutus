## API Gateway

resource "aws_api_gateway_rest_api" "marlowe_symbolic_lambda" {
  name        = "marlowe_symbolic_lambda_${var.env}"
  description = "API Gateway for the Marlowe Symbolic Lambda"
  endpoint_configuration {
    types = ["REGIONAL"]
  }
  binary_media_types = ["image/x-icon", "font/woff2", "font/ttf"]
}

resource "aws_api_gateway_resource" "marlowe_symbolic_proxy" {
  rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  parent_id   = aws_api_gateway_rest_api.marlowe_symbolic_lambda.root_resource_id
  path_part   = "marlowe-analysis"
}

resource "aws_api_gateway_method" "marlowe_symbolic_proxy" {
  rest_api_id   = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  resource_id   = aws_api_gateway_resource.marlowe_symbolic_proxy.id
  http_method   = "POST"
  authorization = "NONE"
  api_key_required = false
}

resource "aws_api_gateway_integration" "marlowe_symbolic_lambda" {
  rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  resource_id = aws_api_gateway_method.marlowe_symbolic_proxy.resource_id
  http_method = aws_api_gateway_method.marlowe_symbolic_proxy.http_method

  integration_http_method = "POST"
  type                    = "AWS"
  uri                     = aws_lambda_function.marlowe_symbolic.invoke_arn

  request_parameters = {
  }
}

resource "aws_api_gateway_method_response" "marlowe_symbolic_lambda" {
  rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  resource_id = aws_api_gateway_resource.marlowe_symbolic_proxy.id
  http_method = aws_api_gateway_method.marlowe_symbolic_proxy.http_method
  status_code = "200"
}

resource "aws_api_gateway_integration_response" "marlowe_symbolic_lambda" {
  rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  resource_id = aws_api_gateway_resource.marlowe_symbolic_proxy.id
  http_method = aws_api_gateway_method.marlowe_symbolic_proxy.http_method
  status_code = aws_api_gateway_method_response.marlowe_symbolic_lambda.status_code
}

resource "aws_api_gateway_deployment" "marlowe_symbolic_lambda" {
  depends_on = [
    aws_api_gateway_integration.marlowe_symbolic_lambda,
  ]

  rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  stage_name  = var.env
}

resource "aws_lambda_permission" "marlowe_symbolic_lambda_api_gw" {
  statement_id  = "AllowAPIGatewayInvoke"
  action        = "lambda:InvokeFunction"
  function_name = aws_lambda_function.marlowe_symbolic.function_name
  principal     = "apigateway.amazonaws.com"

  # The "/*/*" portion grants access from any method on any resource
  # within the API Gateway REST API.
  source_arn = "${aws_api_gateway_rest_api.marlowe_symbolic_lambda.execution_arn}/*/*"
}

resource "aws_lambda_permission" "marlowe_playground_lambda_api_gw" {
  statement_id  = "AllowAPIGatewayInvoke"
  action        = "lambda:InvokeFunction"
  function_name = aws_lambda_function.marlowe_playground.function_name
  principal     = "apigateway.amazonaws.com"

  # The "/*/*" portion grants access from any method on any resource
  # within the API Gateway REST API.
  source_arn = "${aws_api_gateway_rest_api.marlowe_symbolic_lambda.execution_arn}/*/*"
}

resource "aws_api_gateway_usage_plan" "marlowe_symbolic_lambda" {
  name = "marlowe_symbolic_lambda_${var.env}"

  api_stages {
    api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
    stage  = aws_api_gateway_deployment.marlowe_symbolic_lambda.stage_name
  }

  quota_settings {
    limit  = 86400
    offset = 0
    period = "DAY"
  }
}

resource "aws_api_gateway_domain_name" "marlowe_symbolic_lambda" {
  domain_name = local.marlowe_domain_name

  regional_certificate_arn   = data.aws_acm_certificate.marlowe_private.arn
  endpoint_configuration {
    types = ["REGIONAL"]
  }
}

resource "aws_api_gateway_base_path_mapping" "marlowe_symbolic_lambda" {
  # The path, if not specified, is `/` by default
  api_id      = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  stage_name  = aws_api_gateway_deployment.marlowe_symbolic_lambda.stage_name
  domain_name = aws_api_gateway_domain_name.marlowe_symbolic_lambda.domain_name
}

resource "aws_api_gateway_resource" "api" {
   rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
   parent_id   = aws_api_gateway_rest_api.marlowe_symbolic_lambda.root_resource_id
   path_part   = "api"
}

resource "aws_api_gateway_resource" "proxy" {
  depends_on = [
    aws_api_gateway_resource.api,
  ]
   rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
   parent_id   = aws_api_gateway_resource.api.id
   path_part   = "{proxy+}"
}

resource "aws_api_gateway_method" "proxy" {
   rest_api_id   = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
   resource_id   = aws_api_gateway_resource.proxy.id
   http_method   = "ANY"
   authorization = "NONE"
}

resource "aws_api_gateway_integration" "proxy" {
  rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  resource_id = aws_api_gateway_method.proxy.resource_id
  http_method = aws_api_gateway_method.proxy.http_method

  integration_http_method = "POST"
  type                    = "AWS_PROXY"
  uri                     = aws_lambda_function.marlowe_playground.invoke_arn

  request_parameters = {
  }
}

# runghc proxy
resource "aws_api_gateway_resource" "runghc" {
  depends_on = [
    aws_api_gateway_resource.api,
  ]
   rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
   parent_id   = aws_api_gateway_rest_api.marlowe_symbolic_lambda.root_resource_id
   path_part   = "runghc"
}

resource "aws_api_gateway_method" "runghc" {
   rest_api_id   = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
   resource_id   = aws_api_gateway_resource.runghc.id
   http_method   = "POST"
   authorization = "NONE"
}

resource "aws_api_gateway_integration" "runghc" {
  rest_api_id = aws_api_gateway_rest_api.marlowe_symbolic_lambda.id
  resource_id = aws_api_gateway_method.runghc.resource_id
  http_method = aws_api_gateway_method.runghc.http_method

  integration_http_method = "POST"
  type                    = "HTTP_PROXY"
  uri                     = "http://${aws_alb.plutus.dns_name}/runghc"

  request_parameters = {
  }
}

resource "aws_route53_record" "lambda" {
  name    = local.marlowe_domain_name
  type    = "A"
  zone_id = "${var.marlowe_public_zone}"
  alias {
    name                   = "${aws_api_gateway_domain_name.marlowe_symbolic_lambda.regional_domain_name}"
    zone_id                = "${aws_api_gateway_domain_name.marlowe_symbolic_lambda.regional_zone_id}"
    evaluate_target_health = true
  }
}

output "rest_api_id" {
  value = "${aws_api_gateway_rest_api.marlowe_symbolic_lambda.id}"
}

output "region" {
  value = "${var.aws_region}"
}