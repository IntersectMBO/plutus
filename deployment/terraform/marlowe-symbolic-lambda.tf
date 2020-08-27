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
    cidr_blocks = var.private_subnet_cidrs
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
  filename = "${var.symbolic_lambda_file}"
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