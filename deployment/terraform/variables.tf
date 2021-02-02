variable "aws_region" {
}

variable "project" {
  default = "plutus_playground"
}

variable "env" {}

variable "nixops_root" {
  default = "../nixops"
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

variable "nixops_instance_type" {
  default = "t2.large"
}
variable "bastion_ssh_keys" {
  default = {
    alpha = ["david", "pablo"]
    patrick = ["david", "kris"]
    david   = ["david"]
    kris    = ["kris"]
    pablo   = ["pablo"]
    prod = [ "live-infra-staging", "david", "kris", "mpj" ]
    playground = [ "live-infra-staging", "david", "kris", "mpj" ]
    wyohack = ["david", "pablo", "kris"]
    testing = ["david", "pablo", "kris"]
  }

  description = "this should contain the public keys of anyone who wants to access any machine, changing the value for a particular environment will cause the bastion machines to be re-created, this is not a problem but it may take some time."
}

variable "nixops_ssh_keys" {
  default = {
    alpha = ["david", "pablo"]
    patrick = ["david", "kris"]
    david   = ["david"]
    kris    = ["kris"]
    pablo   = ["pablo"]
    prod = [ "live-infra-staging" ]
    playground = [ "live-infra-staging", "kris", "david" ]
    wyohack = ["david", "pablo", "kris"]
    testing = ["david", "pablo", "kris"]
  }

  description = "this should contain the public keys of anyone who wants to access the nixops machine, changing the value for a particular environment will cause the nixops machine to be re-created, this is not a problem but it may take some time."
}

variable "playground_ssh_keys" {
  default = {
    alpha = ["david", "pablo"]
    patrick = ["david", "kris"]
    david   = ["david"]
    kris    = ["kris"]
    pablo   = ["pablo"]
    prod = [ "live-infra-staging", "david", "kris", "mpj" ]
    playground = [ "live-infra-staging", "david", "kris", "mpj" ]
    wyohack = ["david", "pablo", "kris"]
    testing = ["david", "pablo", "kris"]
  }

  description = "this should contain the public keys of anyone who wants to access the playground machines"
}

variable "ssh_keys" {
  default = {
    david            = "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABAQCR931i3C3i8IS6xE/gpSx3RvtLsU0div8G69+KP4tYSyd7X3e73EL8dWfyHJWOVRgorHbDDOOC5qMcNB9vpen9hibRtGEeKUTBypm4vVqhBrPp/lPWU5aqYlulA6HKx5bwcg4Xi1kQofuJz9yQdaqvqTuWbJOibNmAUREGKqpERKNU1vWMY8c9u7EmDm2uKyoFLaLxd6r+w6bBqBy/Q0q8CztGqyi/hcQfznnhT/j0dFu5MwGyQ0z/Ihl58QhUc4NlD9SRlLPa4sBe6UxvB00LhyYP6BveFKUeJyahs4pSvgHis0gD3FbmtxQbRjUqkVcFkv5kj8DlKiGPQWaeVBJx"
    kris             = "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABAQDJKNcFtDKX585wipRkoQvMxLofmoyquVRw0HoWf7zKTokc1e6G/4EpBu/klEqoIsQDCsZtkpWQU90GFc1cAnA2mvJcbJIz8efedrk6onnai/MLZjRzTAMIbjXoASK3sUXUH00W7UdKImox0nPRmmuZUk0g9lLPrt4rpWndrTOqc7H81GtxntZiQVvtjpMObBrKGaBlyt7b6P4M/x63Z55LYpUPcZ0V3ww7BD5xnop977vRvHB7fGv87jWsWlh7gXnC1p1Ykid9l7uVu0gWqZKWeNIqLIo5gCDeJLkH4crX+QLBJebs8GYrLIDqIo7PFfAXPMX7PPbGYbBgLjgH5SlN kris@MacBook-Pro"
    mpj = "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAACAQC3Xw/OJSqbbcKoG2/FtiGrLlLcgB6gWb0OEN3fIfYMTMtMiDpknDliNoRdDZl794FicFmgvvdLtG40ITrxfxxxufP15uD/0yXLL+pA3IavKmV7g5Xn35cKtVEoIm/fIiWh1oLmHgyrC49Op19OxilCSsrJhaJjIE2cj3KFqCOsTMG/p2UjSdrYVSns7PxCUHTMZ/5uF/n9K7nbcHTvYUMBWnsBSaHRmdTDHQWeIuEIg730kIeFjqCNydZX/XeDjXoBAsJuH3YzRvjvneXyZqw4agS1cXQEye843/8SB76PgeSqGU6xxSaXegVE35JqWpO0tlfQ6Rx4aDq8fD23mJYGl3JTuARgVizk7Ot3I2kBEzn9Bm8VUgV+NW16oQjfYKjB0045G6+94e+N9bJKglHxrvZyMVjhGgWY7fqSblRckvYUkpK0C8NB5473J3kH+a59L4jcoelqU0rHe44x0t/RNHkf1gJ5kSHyz5+bmDDSa1pkNxcoxDWvP8c+t9ckFuYSt+7pPLBN99S1Ue3X5Vf/a5MYfel1n9fip/WL6K26RYmsifpYkqJRdpX2/1V13q+ZX7NrLNomvP4zQRpYCUK997K3hLUAVhhftLh/j78gNbmHcBdHVYiYSVAsw9WSf1FPnUPi42Bjx4vAc2WDoHFEmXSGeH/+b/jVvoNKXPTmrQ== michaelpj@gmail.com"
    live-infra-staging = "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIJI+ej2JpsbxyCtScmGZWseA+TeHica1a1hGtTgrX/mi cardano@ip-172-31-26-83.eu-central-1.compute.internal"
    pablo = "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAACAQCeNj/ZQL+nynseTe42O4G5rs4WqyJKEOMcuiVBki2XT/UuoLz40Lw4b54HtwFTaUQQa3zmSJN5u/5KC8TW8nIKF/7fYChqypX3KKBSqBJe0Gul9ncTqHmzpzrwERlh5GkYSH+nr5t8cUK1pBilscKbCxh5x6irOnUmosoKJDv68WKq8WLsjpRslV5/1VztBanFFOZdD3tfIph1Yn7j1DQP4NcT1cQGoBhO0b0vwHtz6vTY4SpHnYuwB1K4dQ3k+gYJUspn03byi/8KVvcerLKfXYFKR5uvRkHihlIwjlxL2FoXIkGhtlkFVFOx76CvEv8LU5AT1ueJ34C/qP6PSD//pezXkk3e4UGeQMLOUu507FjfjHjD4luxIInzBb1KLAjzxb+2B4JTHy2uUu1dpHXarqSyR3DAPcLqUjZajZ+6mQh7zNRgkwXyZqg9p2TOdfiH9dvrqPowocGJgfjsYnd9rfdQVc10h1zk4pP4pP/YhgMVzYYc/ytCqUP41zSsrtJI592PUS9/quDGfrUcuG4t06DJgevky5AGX2og+sR4e83UpgId/DdV/m1OIvuoS4iMrzN2XmZ7IaFxH03nWQPrndDJ3j9ZHiaZ9IyW0XwthJFXcaslL5w3c0+1y8blxhC0vHT4NUsf5vcY3pFrBsMbTt1yNIGcitnLhXC1k99JbQ=="
  }
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
    "ap-east-1" = "ami-0d18fdd309cdefa86"
    "ap-northeast-1" = "ami-093d9cc49c191eb6c"
    "ap-northeast-2" = "ami-0087df91a7b6ebd45"
    "ap-south-1" = "ami-0a1a6b569af04af9d"
    "ap-southeast-1" = "ami-0dbf353e168d155f7"
    "ap-southeast-2" = "ami-04c0f3a75f63daddd"
    "ca-central-1" = "ami-02365684a173255c7"
    "eu-central-1" = "ami-0a1a94722dcbff94c"
    "eu-north-1" = "ami-02699abfacbb6464b"
    "eu-west-1" = "ami-02c34db5766cc7013"
    "eu-west-2" = "ami-0e32bd8c7853883f1"
    "eu-west-3" = "ami-061edb1356c1d69fd"
    "sa-east-1" = "ami-09859378158ae971d"
    "us-east-1" = "ami-0c5e7760748b74e85"
    "us-east-2" = "ami-030296bb256764655"
    "us-west-1" = "ami-050be818e0266b741"
    "us-west-2" = "ami-06562f78dca68eda2"
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
