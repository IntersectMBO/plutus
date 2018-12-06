terraform {
  required_version = "~> 0.11.0"

  backend "s3" {
    bucket = "plutus-playground-tf"
    key    = "state"
    region = "eu-west-1"
  }
}

provider "aws" {
  region  = "${var.aws_region}"
  version = "~> 1.16.0"
}
