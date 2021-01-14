# Static website

## Marlowe Playground
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

resource "aws_iam_role" "marlowe_s3_proxy_role" {
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

## Plutus Playground
resource "aws_s3_bucket" "plutus_playground" {
  bucket = "plutus-playground-website-${var.env}"
  acl    = "public-read"

  website {
    index_document = "index.html"
    error_document = "error.html"
  }
}

resource "aws_s3_bucket_policy" "plutus_playground_website" {
  bucket = aws_s3_bucket.plutus_playground.id

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
                "arn:aws:s3:::plutus-playground-website-${var.env}/*"
            ]
        }
    ]
}
POLICY
}

resource "aws_iam_role" "plutus_s3_proxy_role" {
  name               = "plutus_website_s3_${var.env}"
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