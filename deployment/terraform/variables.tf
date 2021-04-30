# This file contains values that need to be changed at runtime. E.g. `env` and `aws_region` need to be set before running terraform apply
variable "aws_region" {}

variable "env" {}

variable "output_path" {
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

variable "marlowe_web_public_zone" {
  default = "Z09016162N4S3NFVWHXYP"
}

variable "marlowe_web_tld" {
  default = "marlowe-web.iohkdev.io"
}

variable "marlowe_dash_public_zone" {
  default = "Z04600362E06M9P9U3Y12"
}

variable "bastion_instance_type" {
  default = "t3.micro"
}

variable "webghc_instance_type" {
  default = "t3.large"
}

variable "playgrounds_instance_type" {
  default = "t3.small"
}

variable "marlowe_dash_instance_type" {
  default = "t3.small"
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

variable "azs" {
  default = ["a", "b"]
}
