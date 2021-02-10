# This file contains values that need to be changed at runtime. E.g. `env` and `aws_region` need to be set before running terraform apply
variable "aws_region" {}

variable "env" {}

variable "output_path" {
}

variable "ssh_config_root" {
  default = "~/.ssh"
}

variable "plutus_tld" {
  default = "plutus.iohkdev.io"
}

variable "plutus_full_domain" {
  default = ""
}

variable "plutus_public_zone" {
  default = "ZBC2AQBA8QH4G"
}

variable "marlowe_tld" {
  default = "marlowe.iohkdev.io"
}

variable "marlowe_full_domain" {
  default = ""
}

variable "marlowe_public_zone" {
  default = "Z1VIYCTCY8RMLZ"
}

variable "marlowe_dash_tld" {
  default = "marlowe-dash.iohkdev.io"
}

variable "marlowe_dash_public_zone" {
  default = "Z04600362E06M9P9U3Y12"
}

variable "monitoring_tld" {
  default = "goguen.monitoring.iohkdev.io"
}

variable "monitoring_full_domain" {
  default = ""
}

variable "monitoring_public_zone" {
  default = "Z2Y3TWJMJ0Q6Z7"
}

variable "webghc_instance_type" {
  default = "t3.large"
}

variable "playground_instance_type" {
  default = "t3.small"
}

variable "marlowe_dash_instance_type" {
  default = "t3.small"
}

variable "prometheus_instance_type" {
  default = "t2.large"
}

variable "vpc_cidr" {
  default = "10.0.0.0/16"
}

variable "public_subnet_cidrs" {
  default = ["10.0.1.0/24", "10.0.2.0/24", "10.0.3.0/24"]
}

variable "private_subnet_cidrs" {
  default = ["10.0.4.0/24", "10.0.5.0/24", "10.0.6.0/24"]
}

variable "aws_amis" {
  default = {
    "eu-west-1"      = "ami-cda4fab4"
    "eu-west-2"      = "ami-d96786be"
    "eu-west-3"      = "ami-6b0cba16"
    "eu-central-1"   = "ami-5e2b75b5"
    "us-east-1"      = "ami-d464cba9"
    "us-east-2"      = "ami-fd221298"
    "us-west-1"      = "ami-ff0d1d9f"
    "us-west-2"      = "ami-c05c3bb8"
    "ca-central-1"   = "ami-cc72f4a8"
    "ap-southeast-1" = "ami-b61633ca"
    "ap-southeast-2" = "ami-530fc131"
    "ap-northeast-1" = "ami-90d6c0ec"
    "ap-northeast-2" = "ami-a1248bcf"
    "sa-east-1"      = "ami-b090c6dc"
    "ap-south-1"     = "ami-32c9ec5d"
  }
}

variable "amis_20_03" {
  default = {
    "ap-east-1"      = "ami-0d18fdd309cdefa86"
    "ap-northeast-1" = "ami-093d9cc49c191eb6c"
    "ap-northeast-2" = "ami-0087df91a7b6ebd45"
    "ap-south-1"     = "ami-0a1a6b569af04af9d"
    "ap-southeast-1" = "ami-0dbf353e168d155f7"
    "ap-southeast-2" = "ami-04c0f3a75f63daddd"
    "ca-central-1"   = "ami-02365684a173255c7"
    "eu-central-1"   = "ami-0a1a94722dcbff94c"
    "eu-north-1"     = "ami-02699abfacbb6464b"
    "eu-west-1"      = "ami-02c34db5766cc7013"
    "eu-west-2"      = "ami-0e32bd8c7853883f1"
    "eu-west-3"      = "ami-061edb1356c1d69fd"
    "sa-east-1"      = "ami-09859378158ae971d"
    "us-east-1"      = "ami-0c5e7760748b74e85"
    "us-east-2"      = "ami-030296bb256764655"
    "us-west-1"      = "ami-050be818e0266b741"
    "us-west-2"      = "ami-06562f78dca68eda2"
  }
}

variable "azs" {
  default = ["a", "b"]
}

variable "symbolic_lambda_file" {
}

variable "playground_lambda_file" {
}

variable "plutus_playground_lambda_file" {
}

variable "marlowe_github_client_id" {
}

variable "marlowe_github_client_secret" {
}

variable "marlowe_jwt_signature" {
}

variable "plutus_github_client_id" {
}

variable "plutus_github_client_secret" {
}

variable "plutus_jwt_signature" {
}
