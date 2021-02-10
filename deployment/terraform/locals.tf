# This file contains all values that do not need to be set at runtime. For example `env` must be a variable because you need to set the environment
# when you run terraform apply however despite `marlowe_domain_name` depending on the value of `env`, it does not need to be set when you run
# terraform apply as it is an expression that is evaluated based on `env` etc.
locals {
  project = "plutus_playground"

  # By default domain names are structured by environment and type e.g. env.plutus.iohkdev.io but we can override those e.g. prodplutus.iohk.io
  marlowe_domain_name      = "${var.marlowe_full_domain != "" ? var.marlowe_full_domain : "${var.env}.${var.marlowe_tld}"}"
  plutus_domain_name       = "${var.plutus_full_domain != "" ? var.plutus_full_domain : "${var.env}.${var.plutus_tld}"}"
  marlowe_dash_domain_name = "${var.env}.${var.marlowe_dash_tld}"
  monitoring_domain_name   = "${var.monitoring_full_domain != "" ? var.monitoring_full_domain : "${var.env}.${var.monitoring_tld}"}"

  prometheus_port = 9090
  node_exporter_port = 9100

  # SSH Keys
  ssh_keys = {
    david              = "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABAQCR931i3C3i8IS6xE/gpSx3RvtLsU0div8G69+KP4tYSyd7X3e73EL8dWfyHJWOVRgorHbDDOOC5qMcNB9vpen9hibRtGEeKUTBypm4vVqhBrPp/lPWU5aqYlulA6HKx5bwcg4Xi1kQofuJz9yQdaqvqTuWbJOibNmAUREGKqpERKNU1vWMY8c9u7EmDm2uKyoFLaLxd6r+w6bBqBy/Q0q8CztGqyi/hcQfznnhT/j0dFu5MwGyQ0z/Ihl58QhUc4NlD9SRlLPa4sBe6UxvB00LhyYP6BveFKUeJyahs4pSvgHis0gD3FbmtxQbRjUqkVcFkv5kj8DlKiGPQWaeVBJx"
    kris               = "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABAQDJKNcFtDKX585wipRkoQvMxLofmoyquVRw0HoWf7zKTokc1e6G/4EpBu/klEqoIsQDCsZtkpWQU90GFc1cAnA2mvJcbJIz8efedrk6onnai/MLZjRzTAMIbjXoASK3sUXUH00W7UdKImox0nPRmmuZUk0g9lLPrt4rpWndrTOqc7H81GtxntZiQVvtjpMObBrKGaBlyt7b6P4M/x63Z55LYpUPcZ0V3ww7BD5xnop977vRvHB7fGv87jWsWlh7gXnC1p1Ykid9l7uVu0gWqZKWeNIqLIo5gCDeJLkH4crX+QLBJebs8GYrLIDqIo7PFfAXPMX7PPbGYbBgLjgH5SlN kris@MacBook-Pro"
    mpj                = "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAACAQC3Xw/OJSqbbcKoG2/FtiGrLlLcgB6gWb0OEN3fIfYMTMtMiDpknDliNoRdDZl794FicFmgvvdLtG40ITrxfxxxufP15uD/0yXLL+pA3IavKmV7g5Xn35cKtVEoIm/fIiWh1oLmHgyrC49Op19OxilCSsrJhaJjIE2cj3KFqCOsTMG/p2UjSdrYVSns7PxCUHTMZ/5uF/n9K7nbcHTvYUMBWnsBSaHRmdTDHQWeIuEIg730kIeFjqCNydZX/XeDjXoBAsJuH3YzRvjvneXyZqw4agS1cXQEye843/8SB76PgeSqGU6xxSaXegVE35JqWpO0tlfQ6Rx4aDq8fD23mJYGl3JTuARgVizk7Ot3I2kBEzn9Bm8VUgV+NW16oQjfYKjB0045G6+94e+N9bJKglHxrvZyMVjhGgWY7fqSblRckvYUkpK0C8NB5473J3kH+a59L4jcoelqU0rHe44x0t/RNHkf1gJ5kSHyz5+bmDDSa1pkNxcoxDWvP8c+t9ckFuYSt+7pPLBN99S1Ue3X5Vf/a5MYfel1n9fip/WL6K26RYmsifpYkqJRdpX2/1V13q+ZX7NrLNomvP4zQRpYCUK997K3hLUAVhhftLh/j78gNbmHcBdHVYiYSVAsw9WSf1FPnUPi42Bjx4vAc2WDoHFEmXSGeH/+b/jVvoNKXPTmrQ== michaelpj@gmail.com"
    live-infra-staging = "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIJI+ej2JpsbxyCtScmGZWseA+TeHica1a1hGtTgrX/mi cardano@ip-172-31-26-83.eu-central-1.compute.internal"
    pablo              = "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAACAQCeNj/ZQL+nynseTe42O4G5rs4WqyJKEOMcuiVBki2XT/UuoLz40Lw4b54HtwFTaUQQa3zmSJN5u/5KC8TW8nIKF/7fYChqypX3KKBSqBJe0Gul9ncTqHmzpzrwERlh5GkYSH+nr5t8cUK1pBilscKbCxh5x6irOnUmosoKJDv68WKq8WLsjpRslV5/1VztBanFFOZdD3tfIph1Yn7j1DQP4NcT1cQGoBhO0b0vwHtz6vTY4SpHnYuwB1K4dQ3k+gYJUspn03byi/8KVvcerLKfXYFKR5uvRkHihlIwjlxL2FoXIkGhtlkFVFOx76CvEv8LU5AT1ueJ34C/qP6PSD//pezXkk3e4UGeQMLOUu507FjfjHjD4luxIInzBb1KLAjzxb+2B4JTHy2uUu1dpHXarqSyR3DAPcLqUjZajZ+6mQh7zNRgkwXyZqg9p2TOdfiH9dvrqPowocGJgfjsYnd9rfdQVc10h1zk4pP4pP/YhgMVzYYc/ytCqUP41zSsrtJI592PUS9/quDGfrUcuG4t06DJgevky5AGX2og+sR4e83UpgId/DdV/m1OIvuoS4iMrzN2XmZ7IaFxH03nWQPrndDJ3j9ZHiaZ9IyW0XwthJFXcaslL5w3c0+1y8blxhC0vHT4NUsf5vcY3pFrBsMbTt1yNIGcitnLhXC1k99JbQ=="
  }

  # Anyone who wants ssh access to a machine needs ssh access to the bastion hosts (i.e. both root and monitoring users should be in here)
  bastion_ssh_keys_ks = {
    alpha      = ["david", "pablo"]
    patrick    = ["david", "kris"]
    david      = ["david"]
    kris       = ["kris"]
    pablo      = ["pablo"]
    prod       = ["live-infra-staging", "david", "kris", "mpj"]
    playground = ["live-infra-staging", "david", "kris", "mpj"]
    wyohack    = ["david", "pablo", "kris"]
    testing    = ["david", "pablo", "kris"]
  }
  bastion_ssh_keys = [for k in local.bastion_ssh_keys_ks[var.env] : local.ssh_keys[k]]

  # There is a special user with limited permissions that can log on to machines to view logs etc
  monitoring_ssh_keys_ks = {
    alpha      = ["david", "pablo"]
    patrick    = ["david", "kris"]
    david      = ["david"]
    kris       = ["kris"]
    pablo      = ["pablo"]
    prod       = ["live-infra-staging"]
    playground = ["live-infra-staging", "kris", "david"]
    wyohack    = ["david", "pablo", "kris"]
    testing    = ["david", "pablo", "kris"]
  }
  monitoring_ssh_keys = [for k in local.monitoring_ssh_keys_ks[var.env] : local.ssh_keys[k]]

  # root users are able to deploy to the machines using morph
  root_ssh_keys_ks = {
    alpha      = ["david", "pablo"]
    patrick    = ["david", "kris"]
    david      = ["david"]
    kris       = ["kris"]
    pablo      = ["pablo"]
    prod       = ["live-infra-staging", "david", "kris", "mpj"]
    playground = ["live-infra-staging", "david", "kris", "mpj"]
    wyohack    = ["david", "pablo", "kris"]
    testing    = ["david", "pablo", "kris"]
  }
  root_ssh_keys = [for k in local.root_ssh_keys_ks[var.env] : local.ssh_keys[k]]

}

module "nixos_image" {
    source  = "git::https://github.com/tweag/terraform-nixos.git//aws_image_nixos?ref=5f5a0408b299874d6a29d1271e9bffeee4c9ca71"
    release = "20.09"
}