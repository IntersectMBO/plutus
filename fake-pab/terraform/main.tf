terraform {
  required_version = "~> 0.12.20"

  backend "s3" {
    bucket  = "fake-pab-tf"
    key     = "state"
    region  = "eu-west-2"
    profile = "fake-pab"
  }
}

provider "aws" {
  region  = "eu-west-2"
  version = "3.24.1"
  profile = "fake-pab"
}
