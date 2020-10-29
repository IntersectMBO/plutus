data "template_file" "playground_ssh_keys" {
  template = "$${ssh_key}"
  count    = "${length(var.playground_ssh_keys["${var.env}"])}"

  vars = {
    ssh_key = "${var.ssh_keys["${element(var.playground_ssh_keys["${var.env}"], count.index)}"]}"
  }
}

locals {
  webghcA = {
    name = "webghcA"
    ip   = "${element(concat(aws_instance.webghc_a.*.private_ip, list("")), 0)}"
    dns  = "webghc-a.${element(concat(aws_route53_zone.plutus_private_zone.*.name, list("")), 0)}"
  }

  webghcB = {
    name = "webghcB"
    ip   = "${element(concat(aws_instance.webghc_b.*.private_ip, list("")), 0)}"
    dns  = "webghc-b.${element(concat(aws_route53_zone.plutus_private_zone.*.name, list("")), 0)}"
  }

  nixops = {
    name = "nixops"
    ip   = "${element(concat(aws_instance.nixops.*.private_ip, list("")), 0)}"
    dns  = "nixops.${element(concat(aws_route53_zone.plutus_private_zone.*.name, list("")), 0)}"
    externalDns = "${local.monitoring_domain_name}"
  }

  bastionA = {
    name = "bastion-a"
    ip   = "${element(aws_instance.bastion.*.public_ip, 0)}"
    dns  = ""
  }

  machines = {
    webghcA       = "${local.webghcA}"
    webghcB       = "${local.webghcB}"
    nixops         = "${local.nixops}"
    playgroundSshKeys = "${data.template_file.playground_ssh_keys.*.rendered}"
    rootSshKeys = "${data.template_file.nixops_ssh_keys.*.rendered}"
    awsRegion      = "${var.aws_region}"
    environment    = "${var.env}"
    project        = "${var.project}"
    tld            = "${var.plutus_tld}"
    plutusTld     = "${var.plutus_tld}"
    marloweTld     = "${var.marlowe_tld}"
  }

  bastionMachines = {
    bastionA = "${local.bastionA}"
  }
}

resource "local_file" "bastion_machines" {
  content  = jsonencode(local.bastionMachines)
  filename = "${pathexpand(var.nixops_root)}/bastion_machines.json"
}

resource "local_file" "machines" {
  content  = jsonencode(local.machines)
  filename = "${pathexpand(var.nixops_root)}/machines.json"
}
