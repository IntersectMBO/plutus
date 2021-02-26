# This produces a json file with the names and addresses of all the EC2 instances that can then be used by morph
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

  marloweDashA = {
    name = "marloweDashA"
    ip   = "${element(concat(aws_instance.marlowe_dash_a.*.private_ip, list("")), 0)}"
    dns  = "marlowe-dash-a.${element(concat(aws_route53_zone.plutus_private_zone.*.name, list("")), 0)}"
  }

  marloweDashB = {
    name = "marloweDashB"
    ip   = "${element(concat(aws_instance.marlowe_dash_b.*.private_ip, list("")), 0)}"
    dns  = "marlowe-dash-b.${element(concat(aws_route53_zone.plutus_private_zone.*.name, list("")), 0)}"
  }

  playgroundsA = {
    name = "playgroundsA"
    ip   = "${element(concat(aws_instance.playgrounds_a.*.private_ip, list("")), 0)}"
    dns  = "playgrounds-a.${element(concat(aws_route53_zone.plutus_private_zone.*.name, list("")), 0)}"
  }

  playgroundsB = {
    name = "playgroundsB"
    ip   = "${element(concat(aws_instance.playgrounds_b.*.private_ip, list("")), 0)}"
    dns  = "playgrounds-b.${element(concat(aws_route53_zone.plutus_private_zone.*.name, list("")), 0)}"
  }

  prometheus = {
    name        = "prometheus"
    ip          = "${element(concat(aws_instance.prometheus.*.private_ip, list("")), 0)}"
    dns         = "prometheus.${element(concat(aws_route53_zone.plutus_private_zone.*.name, list("")), 0)}"
    externalDns = "${local.monitoring_domain_name}"
  }

  machines = {
    webghcA           = "${local.webghcA}"
    webghcB           = "${local.webghcB}"
    marloweDashA      = "${local.marloweDashA}"
    marloweDashB      = "${local.marloweDashB}"
    playgroundsA      = "${local.playgroundsA}"
    playgroundsB      = "${local.playgroundsB}"
    prometheus            = "${local.prometheus}"
    rootSshKeys       = local.root_ssh_keys
    monitoringSshKeys = local.monitoring_ssh_keys
    awsRegion         = "${var.aws_region}"
    environment       = "${var.env}"
    project           = "${local.project}"
    tld               = "${var.plutus_tld}"
    plutusTld         = "${var.plutus_tld}"
    marloweTld        = "${var.marlowe_tld}"
  }
}

resource "local_file" "machines" {
  content  = jsonencode(local.machines)
  filename = "${pathexpand(var.output_path)}/machines.json"
}
