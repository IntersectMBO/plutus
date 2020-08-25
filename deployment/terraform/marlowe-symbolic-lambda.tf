# Security Group
resource "aws_security_group" "marlowe_symbolic_lambda" {
  vpc_id = "${aws_vpc.plutus.id}"

  ## inbound (world): ICMP 3:4 "Fragmentation Needed and Don't Fragment was Set"
  ingress {
    from_port   = "3"
    to_port     = "4"
    protocol    = "ICMP"
    cidr_blocks = ["0.0.0.0/0"]
  }

  ## outgoing: private subnet
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["${var.private_subnet_cidrs}"]
  }

  tags = {
    Name        = "${var.project}_${var.env}_marlowe_symbolic_lambda"
    Project     = "${var.project}"
    Environment = "${var.env}"
  }
}

resource "aws_iam_role" "marlowe_symbolic_lambda" {
  name = "marlowe_symbolic_lambda_${var.env}"

  assume_role_policy = <<EOF
{
  "Version": "2012-10-17",
  "Statement": [
    {
      "Action": "sts:AssumeRole",
      "Principal": {
        "Service": "lambda.amazonaws.com"
      },
      "Effect": "Allow",
      "Sid": ""
    }
  ]
}
EOF
}

resource "aws_iam_role_policy_attachment" "marlowe_symbolic_lambda" {
  role = "${aws_iam_role.marlowe_symbolic_lambda.name}"
  policy_arn = "arn:aws:iam::aws:policy/service-role/AWSLambdaVPCAccessExecutionRole"
}

resource "aws_lambda_function" "marlowe_symbolic" {
  function_name = "marlowe_symbolic_${var.env}"
  role          = "${aws_iam_role.marlowe_symbolic_lambda.arn}"
  handler       = "src/App.handler"

  runtime = "provided"

  # The lambda zip needs to be built and placed on your local filesystem
  # TODO: This is only a temporary requirement and will be moved to the CD server soon
  filename = "${var.lambda_filename}"
  source_code_hash = "${base64sha256(file(var.lambda_filename))}"
  
  memory_size = 3008
  timeout = 120
  publish = true

  environment {
    variables = {
      SBV_Z3 = "z3"
      PATH = "/usr/local/bin:/usr/bin/:/bin:/opt/bin:."
    }
  }
}


## API Gateway

resource "aws_api_gateway_rest_api" "marlowe_symbolic_lambda" {
  name        = "marlowe_symbolic_lambda_${var.env}"
  description = "API Gateway for the Marlowe Symbolic Lambda"
  endpoint_configuration {
    types = ["REGIONAL"]
  }
}

resource "aws_api_gateway_resource" "marlowe_symbolic_proxy" {
  rest_api_id = "${aws_api_gateway_rest_api.marlowe_symbolic_lambda.id}"
  parent_id   = "${aws_api_gateway_rest_api.marlowe_symbolic_lambda.root_resource_id}"
  path_part   = "marlowe-analysis"
}

resource "aws_api_gateway_method" "marlowe_symbolic_proxy" {
  rest_api_id   = "${aws_api_gateway_rest_api.marlowe_symbolic_lambda.id}"
  resource_id   = "${aws_api_gateway_resource.marlowe_symbolic_proxy.id}"
  http_method   = "POST"
  authorization = "NONE"
  api_key_required = true
}

resource "aws_api_gateway_integration" "marlowe_symbolic_lambda" {
  rest_api_id = "${aws_api_gateway_rest_api.marlowe_symbolic_lambda.id}"
  resource_id = "${aws_api_gateway_method.marlowe_symbolic_proxy.resource_id}"
  http_method = "${aws_api_gateway_method.marlowe_symbolic_proxy.http_method}"

  integration_http_method = "POST"
  type                    = "AWS"
  uri                     = "${aws_lambda_function.marlowe_symbolic.invoke_arn}"

  request_parameters = {
  }
}

resource "aws_api_gateway_method_response" "marlowe_symbolic_lambda" {
  rest_api_id = "${aws_api_gateway_rest_api.marlowe_symbolic_lambda.id}"
  resource_id = "${aws_api_gateway_resource.marlowe_symbolic_proxy.id}"
  http_method = "${aws_api_gateway_method.marlowe_symbolic_proxy.http_method}"
  status_code = "200"
}

resource "aws_api_gateway_integration_response" "marlowe_symbolic_lambda" {
  rest_api_id = "${aws_api_gateway_rest_api.marlowe_symbolic_lambda.id}"
  resource_id = "${aws_api_gateway_resource.marlowe_symbolic_proxy.id}"
  http_method = "${aws_api_gateway_method.marlowe_symbolic_proxy.http_method}"
  status_code = "${aws_api_gateway_method_response.marlowe_symbolic_lambda.status_code}"
}

resource "aws_api_gateway_deployment" "marlowe_symbolic_lambda" {
  depends_on = [
    "aws_api_gateway_integration.marlowe_symbolic_lambda",
  ]

  rest_api_id = "${aws_api_gateway_rest_api.marlowe_symbolic_lambda.id}"
  stage_name  = "${var.env}"
}

resource "aws_lambda_permission" "marlowe_symbolic_lambda_api_gw" {
  statement_id  = "AllowAPIGatewayInvoke"
  action        = "lambda:InvokeFunction"
  function_name = "${aws_lambda_function.marlowe_symbolic.function_name}"
  principal     = "apigateway.amazonaws.com"

  # The "/*/*" portion grants access from any method on any resource
  # within the API Gateway REST API.
  source_arn = "${aws_api_gateway_rest_api.marlowe_symbolic_lambda.execution_arn}/*/*"
}

resource "aws_api_gateway_usage_plan" "marlowe_symbolic_lambda" {
  name = "marlowe_symbolic_lambda_${var.env}"

  api_stages {
    api_id = "${aws_api_gateway_rest_api.marlowe_symbolic_lambda.id}"
    stage  = "${aws_api_gateway_deployment.marlowe_symbolic_lambda.stage_name}"
  }
}

resource "aws_api_gateway_api_key" "marlowe_symbolic_lambda" {
  name = "marlowe_symbolic_lambda_${var.env}"
}

resource "aws_api_gateway_usage_plan_key" "marlowe_symbolic_lambda" {
  key_id        = "${aws_api_gateway_api_key.marlowe_symbolic_lambda.id}"
  key_type      = "API_KEY"
  usage_plan_id = "${aws_api_gateway_usage_plan.marlowe_symbolic_lambda.id}"
}
