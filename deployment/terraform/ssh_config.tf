data "template_file" "ssh_config_section_nixops" {
  template = "${file("${path.module}/templates/ssh-config")}"

  vars {
    full_hostname    = "nixops.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "nixops.${var.project}"
    ip               = "${aws_instance.nixops.private_ip}"
    bastion_hostname = "${aws_instance.bastion.*.public_ip[0]}"
    user_name        = "nixops"
  }
}

data "template_file" "ssh_config_section_playground_a" {
  template = "${file("${path.module}/templates/ssh-config")}"

  vars {
    full_hostname    = "playground-a.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "playground-a.${var.project}"
    ip               = "${aws_instance.playground_a.private_ip}"
    bastion_hostname = "${aws_instance.bastion.*.public_ip[0]}"
    user_name        = "plutus"
  }
}

data "template_file" "ssh_config_section_playground_b" {
  template = "${file("${path.module}/templates/ssh-config")}"

  vars {
    full_hostname    = "playground-b.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "playground-b.${var.project}"
    ip               = "${aws_instance.playground_b.private_ip}"
    bastion_hostname = "${aws_instance.bastion.*.public_ip[0]}"
    user_name        = "plutus"
  }
}

data "template_file" "ssh_config_section_meadow_a" {
  template = "${file("${path.module}/templates/ssh-config")}"

  vars {
    full_hostname    = "meadow-a.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "meadow-a.${var.project}"
    ip               = "${aws_instance.meadow_a.private_ip}"
    bastion_hostname = "${aws_instance.bastion.*.public_ip[0]}"
    user_name        = "plutus"
  }
}

data "template_file" "ssh_config_section_meadow_b" {
  template = "${file("${path.module}/templates/ssh-config")}"

  vars {
    full_hostname    = "meadow-b.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "meadow-b.${var.project}"
    ip               = "${aws_instance.meadow_b.private_ip}"
    bastion_hostname = "${aws_instance.bastion.*.public_ip[0]}"
    user_name        = "plutus"
  }
}
data "template_file" "ssh_config" {
  template = "\n$${nixops_node}\n$${playground_a}\n$${playground_b}\n$${meadow_a}\n$${meadow_b}"

  vars {
    nixops_node      = "${data.template_file.ssh_config_section_nixops.rendered}"
    playground_a     = "${data.template_file.ssh_config_section_playground_a.rendered}"
    playground_b     = "${data.template_file.ssh_config_section_playground_b.rendered}"
    meadow_a         = "${data.template_file.ssh_config_section_meadow_a.rendered}"
    meadow_b         = "${data.template_file.ssh_config_section_meadow_b.rendered}"
  }
}

resource "local_file" "ssh_config" {
  content  = "${data.template_file.ssh_config.rendered}"
  filename = "${var.ssh_config_root}/config.d/${var.project}.conf"
}
