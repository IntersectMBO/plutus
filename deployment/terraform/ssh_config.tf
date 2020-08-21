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

data "template_file" "ssh_config_section_marlowe_a" {
  template = "${file("${path.module}/templates/ssh-config")}"

  vars {
    full_hostname    = "marlowe-a.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "marlowe-a.${var.project}"
    ip               = "${aws_instance.marlowe_a.private_ip}"
    bastion_hostname = "${aws_instance.bastion.*.public_ip[0]}"
    user_name        = "plutus"
  }
}

data "template_file" "ssh_config_section_marlowe_b" {
  template = "${file("${path.module}/templates/ssh-config")}"

  vars {
    full_hostname    = "marlowe-b.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "marlowe-b.${var.project}"
    ip               = "${aws_instance.marlowe_b.private_ip}"
    bastion_hostname = "${aws_instance.bastion.*.public_ip[0]}"
    user_name        = "plutus"
  }
}

data "template_file" "ssh_config_section_webghc_a" {
  template = "${file("${path.module}/templates/ssh-config")}"

  vars {
    full_hostname    = "webghc-a.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "webghc-a.${var.project}"
    ip               = "${aws_instance.webghc_a.private_ip}"
    bastion_hostname = "${aws_instance.bastion.*.public_ip[0]}"
    user_name        = "monitoring"
  }
}

data "template_file" "ssh_config_section_webghc_b" {
  template = "${file("${path.module}/templates/ssh-config")}"

  vars {
    full_hostname    = "webghc-b.${aws_route53_zone.plutus_private_zone.name}"
    short_hostname   = "webghc-b.${var.project}"
    ip               = "${aws_instance.webghc_b.private_ip}"
    bastion_hostname = "${aws_instance.bastion.*.public_ip[0]}"
    user_name        = "monitoring"
  }
}

data "template_file" "ssh_config" {
  template = "\n$${nixops_node}\n$${playground_a}\n$${playground_b}\n$${marlowe_a}\n$${marlowe_b}\n$${webghc_a}\n$${webghc_b}"

  vars {
    nixops_node      = "${data.template_file.ssh_config_section_nixops.rendered}"
    playground_a     = "${data.template_file.ssh_config_section_playground_a.rendered}"
    playground_b     = "${data.template_file.ssh_config_section_playground_b.rendered}"
    marlowe_a         = "${data.template_file.ssh_config_section_marlowe_a.rendered}"
    marlowe_b         = "${data.template_file.ssh_config_section_marlowe_b.rendered}"
    webghc_a         = "${data.template_file.ssh_config_section_webghc_a.rendered}"
    webghc_b         = "${data.template_file.ssh_config_section_webghc_b.rendered}"
  }
}

resource "local_file" "ssh_config" {
  content  = "${data.template_file.ssh_config.rendered}"
  filename = "${var.ssh_config_root}/config.d/${var.project}.conf"
}
