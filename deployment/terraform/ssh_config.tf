data "template_file" "ssh_config_section_nixops" {
  template = file("${path.module}/templates/ssh-config")

  vars = {
    full_hostname    = "nixops.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "nixops.${var.project}"
    ip               = aws_instance.nixops.private_ip
    bastion_hostname = aws_instance.bastion.*.public_ip[0]
    user_name        = "root"
  }
}

data "template_file" "ssh_config_section_webghc_a" {
  template = file("${path.module}/templates/ssh-config")

  vars = {
    full_hostname    = "webghc-a.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "webghc-a.${var.project}"
    ip               = aws_instance.webghc_a.private_ip
    bastion_hostname = aws_instance.bastion.*.public_ip[0]
    user_name        = "monitoring"
  }
}

data "template_file" "ssh_config_section_webghc_b" {
  template = file("${path.module}/templates/ssh-config")

  vars = {
    full_hostname    = "webghc-b.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "webghc-b.${var.project}"
    ip               = aws_instance.webghc_b.private_ip
    bastion_hostname = aws_instance.bastion.*.public_ip[0]
    user_name        = "monitoring"
  }
}
data "template_file" "ssh_config_section_marlowe_dash_a" {
  template = file("${path.module}/templates/ssh-config")

  vars = {
    full_hostname    = "marlowe-dash-a.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "marlowe-dash-a.${var.project}"
    ip               = aws_instance.marlowe_dash_a.private_ip
    bastion_hostname = aws_instance.bastion.*.public_ip[0]
    user_name        = "root"
  }
}

data "template_file" "ssh_config_section_marlowe_dash_b" {
  template = file("${path.module}/templates/ssh-config")

  vars = {
    full_hostname    = "marlowe-dash-b.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "marlowe-dash-b.${var.project}"
    ip               = aws_instance.marlowe_dash_b.private_ip
    bastion_hostname = aws_instance.bastion.*.public_ip[0]
    user_name        = "root"
  }
}

data "template_file" "ssh_config" {
  template = "\n$${nixops_node}\n$${webghc_a}\n$${webghc_b}\n$${marlowe_dash_a}\n$${marlowe_dash_b}"

  vars = {
    nixops_node    = data.template_file.ssh_config_section_nixops.rendered
    webghc_a       = data.template_file.ssh_config_section_webghc_a.rendered
    webghc_b       = data.template_file.ssh_config_section_webghc_b.rendered
    marlowe_dash_a = data.template_file.ssh_config_section_marlowe_dash_a.rendered
    marlowe_dash_b = data.template_file.ssh_config_section_marlowe_dash_b.rendered
  }
}

resource "local_file" "ssh_config" {
  content  = data.template_file.ssh_config.rendered
  filename = "${pathexpand(var.ssh_config_root)}/config.d/${var.project}.conf"
}
