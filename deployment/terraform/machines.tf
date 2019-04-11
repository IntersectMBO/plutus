data "template_file" "playground_ssh_keys" {
  template = "$${ssh_key}"
  count    = "${length(var.playground_ssh_keys["${var.env}"])}"

  vars {
    ssh_key = "${var.ssh_keys["${element(var.playground_ssh_keys["${var.env}"], count.index)}"]}"
  }
}

locals {
  playgroundA = {
    name = "playgroundA"
    ip   = "${element(concat(aws_instance.playground_a.*.private_ip, list("")), 0)}"
    dns  = "playground-a.${element(concat(aws_route53_zone.plutus_private_zone.*.name, list("")), 0)}"
  }

  playgroundB = {
    name = "playgroundB"
    ip   = "${element(concat(aws_instance.playground_b.*.private_ip, list("")), 0)}"
    dns  = "playground-b.${element(concat(aws_route53_zone.plutus_private_zone.*.name, list("")), 0)}"
  }
  meadowA = {
    name = "meadowA"
    ip   = "${element(concat(aws_instance.meadow_a.*.private_ip, list("")), 0)}"
    dns  = "meadow-a.${element(concat(aws_route53_zone.plutus_private_zone.*.name, list("")), 0)}"
  }

  meadowB = {
    name = "meadowB"
    ip   = "${element(concat(aws_instance.meadow_b.*.private_ip, list("")), 0)}"
    dns  = "meadow-b.${element(concat(aws_route53_zone.plutus_private_zone.*.name, list("")), 0)}"
  }

  nixops = {
    name = "nixops"
    ip   = "${element(concat(aws_instance.nixops.*.private_ip, list("")), 0)}"
    dns  = "nixops.${element(concat(aws_route53_zone.plutus_private_zone.*.name, list("")), 0)}"
    externalDns = "monitoring.${var.monitoring_tld}"
  }

  bastionA = {
    name = "bastion-a"
    ip   = "${element(aws_instance.bastion.*.public_ip, 0)}"
    dns  = ""
  }

  machines = {
    playgroundA       = "${local.playgroundA}"
    playgroundB       = "${local.playgroundB}"
    meadowA       = "${local.meadowA}"
    meadowB       = "${local.meadowB}"
    nixops         = "${local.nixops}"
    playgroundSshKeys = "${data.template_file.playground_ssh_keys.*.rendered}"
    rootSshKeys = "${data.template_file.nixops_ssh_keys.*.rendered}"
    awsRegion      = "${var.aws_region}"
    environment    = "${var.env}"
    project        = "${var.project}"
    tld            = "${var.plutus_tld}"
    plutusTld     = "${var.plutus_tld}"
    marloweTld     = "${var.meadow_tld}"
  }

  bastionMachines = {
    bastionA = "${local.bastionA}"
  }
}

resource "local_file" "bastion_machines" {
  content  = "${jsonencode(local.bastionMachines)}"
  filename = "${var.nixops_root}/bastion_machines.json"
}

resource "local_file" "machines" {
  content  = "${jsonencode(local.machines)}"
  filename = "${var.nixops_root}/machines.json"
}
