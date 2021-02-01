terraform {
  required_version = "~> 0.12.20"

  backend "s3" {
    bucket = "plutus-playground-tf"
    key    = "state"
    region = "eu-west-1"
    profile = "plutus-playground"
  }
}

provider "aws" {
  region  = var.aws_region
  version = "3.24.1"
  profile = "plutus-playground"
}
