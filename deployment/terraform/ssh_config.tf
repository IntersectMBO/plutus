data "template_file" "ssh_config_section_webghc_a" {
  template = file("${path.module}/templates/ssh-config")

  vars = {
    full_hostname    = "webghc-a.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "webghc-a.${local.project}"
    ip               = aws_instance.webghc_a.private_ip
    bastion_hostname = aws_instance.bastion.*.public_ip[0]
    user_name        = "root"
  }
}

data "template_file" "ssh_config_section_marlowe_dash_a" {
  template = file("${path.module}/templates/ssh-config")

  vars = {
    full_hostname    = "marlowe-dash-a.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "marlowe-dash-a.${local.project}"
    ip               = aws_instance.marlowe_dash_a.private_ip
    bastion_hostname = aws_instance.bastion.*.public_ip[0]
    user_name        = "root"
  }
}

data "template_file" "ssh_config_section_marlowe_dash_b" {
  template = file("${path.module}/templates/ssh-config")

  vars = {
    full_hostname    = "marlowe-dash-b.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "marlowe-dash-b.${local.project}"
    ip               = aws_instance.marlowe_dash_b.private_ip
    bastion_hostname = aws_instance.bastion.*.public_ip[0]
    user_name        = "root"
  }
}
data "template_file" "ssh_config_section_playgrounds_a" {
  template = file("${path.module}/templates/ssh-config")

  vars = {
    full_hostname    = "playgrounds-a.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "playgrounds-a.${local.project}"
    ip               = aws_instance.playgrounds_a.private_ip
    bastion_hostname = aws_instance.bastion.*.public_ip[0]
    user_name        = "root"
  }
}

data "template_file" "ssh_config_section_playgrounds_b" {
  template = file("${path.module}/templates/ssh-config")

  vars = {
    full_hostname    = "playgrounds-b.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "playgrounds-b.${local.project}"
    ip               = aws_instance.playgrounds_b.private_ip
    bastion_hostname = aws_instance.bastion.*.public_ip[0]
    user_name        = "root"
  }
}

data "template_file" "ssh_config" {
  template = <<EOT
$${webghc_a}

$${marlowe_dash_a}

$${marlowe_dash_b}

$${playgrounds_a}

$${playgrounds_b}

Host $${bastion_hostname}
  StrictHostKeyChecking no
EOT

  vars = {
    webghc_a         = data.template_file.ssh_config_section_webghc_a.rendered
    marlowe_dash_a   = data.template_file.ssh_config_section_marlowe_dash_a.rendered
    marlowe_dash_b   = data.template_file.ssh_config_section_marlowe_dash_b.rendered
    playgrounds_a    = data.template_file.ssh_config_section_playgrounds_a.rendered
    playgrounds_b    = data.template_file.ssh_config_section_playgrounds_b.rendered
    bastion_hostname = aws_instance.bastion.*.public_ip[0]
  }
}

resource "local_file" "ssh_config" {
  content  = data.template_file.ssh_config.rendered
  filename = "${pathexpand(var.output_path)}/${local.project}.${var.env}.conf"
}
