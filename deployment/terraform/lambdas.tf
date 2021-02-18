# Security Group
resource "aws_security_group" "marlowe_symbolic_lambda" {
  vpc_id = aws_vpc.plutus.id

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
    cidr_blocks = var.private_subnet_cidrs
  }

  tags = {
    Name        = "${local.project}_${var.env}_marlowe_symbolic_lambda"
    Project     = local.project
    Environment = var.env
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
  role = aws_iam_role.marlowe_symbolic_lambda.name
  policy_arn = "arn:aws:iam::aws:policy/service-role/AWSLambdaVPCAccessExecutionRole"
}

resource "aws_lambda_function" "marlowe_symbolic" {
  function_name = "marlowe_symbolic_${var.env}"
  role          = aws_iam_role.marlowe_symbolic_lambda.arn
  handler       = "src/Marlowe/Symbolic/Lambda.handler"

  runtime = "provided"

  # The lambda zip needs to be built and placed on your local filesystem
  # TODO: This is only a temporary requirement and will be moved to the CD server soon
  filename = var.symbolic_lambda_file
  source_code_hash = filebase64sha256(var.symbolic_lambda_file)

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

resource "aws_lambda_function" "marlowe_playground" {
  function_name = "marlowe_playground_${var.env}"
  role          = aws_iam_role.marlowe_symbolic_lambda.arn
  handler       = "src/Lambda.handler"

  runtime = "provided"

  # The lambda zip needs to be built and placed on your local filesystem
  # TODO: This is only a temporary requirement and will be moved to the CD server soon
  filename = var.playground_lambda_file
  source_code_hash = filebase64sha256(var.playground_lambda_file)

  memory_size = 3008
  timeout = 120
  publish = true

  environment {
    variables = {
      PATH = "/usr/local/bin:/usr/bin/:/bin:/opt/bin:."
      GITHUB_CLIENT_ID = var.marlowe_github_client_id
      GITHUB_CLIENT_SECRET = var.marlowe_github_client_secret
      JWT_SIGNATURE = var.marlowe_jwt_signature
      FRONTEND_URL = "https://${var.env}.${var.marlowe_tld}"
      GITHUB_CALLBACK_PATH = "/#/gh-oauth-cb"
    }
  }
}

resource "aws_lambda_function" "plutus_playground" {
  function_name = "plutus_playground_${var.env}"
  role          = aws_iam_role.marlowe_symbolic_lambda.arn
  handler       = "src/Playground/Lambda.handler"

  runtime = "provided"

  # The lambda zip needs to be built and placed on your local filesystem
  # TODO: This is only a temporary requirement and will be moved to the CD server soon
  filename = var.plutus_playground_lambda_file
  source_code_hash = filebase64sha256(var.plutus_playground_lambda_file)

  memory_size = 3008
  timeout = 120
  publish = true

  environment {
    variables = {
      PATH = "/usr/local/bin:/usr/bin/:/bin:/opt/bin:."
      GITHUB_CLIENT_ID = var.plutus_github_client_id
      GITHUB_CLIENT_SECRET = var.plutus_github_client_secret
      JWT_SIGNATURE = var.plutus_jwt_signature
      FRONTEND_URL = "https://${var.env}.${var.plutus_tld}"
      GITHUB_CALLBACK_PATH = "/api/oauth/github/callback"
      WEBGHC_URL = "https://${var.env}.${var.plutus_tld}"
    }
  }
}
