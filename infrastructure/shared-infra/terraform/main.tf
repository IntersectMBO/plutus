terraform {
  required_version = "~> 0.12.20"

  backend "s3" {
    bucket = "dev-mantis"
    key    = "state"
    region = "eu-west-1"
    profile = "dev-mantis"
  }
}

provider "aws" {
  region  = "eu-west-1"
  version = "~> 3.0"
  profile = "dev-mantis"
}
