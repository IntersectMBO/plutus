# Security Group
resource "aws_security_group" "marlowe" {
  vpc_id = "${aws_vpc.plutus.id}"
  name   = "${var.project}_${var.env}_marlowe"

  ingress {
    from_port   = 22
    to_port     = 22
    protocol    = "TCP"
    cidr_blocks = concat(var.public_subnet_cidrs, var.private_subnet_cidrs)
  }

  ## inbound (world): http

  ingress {
    from_port   = 80
    to_port     = 80
    protocol    = "TCP"
    cidr_blocks = concat(var.public_subnet_cidrs, var.private_subnet_cidrs)
  }

  ingress {
    from_port   = 9100
    to_port     = 9100
    protocol    = "TCP"
    cidr_blocks = var.private_subnet_cidrs
  }

  ingress {
    from_port   = 9091
    to_port     = 9091
    protocol    = "TCP"
    cidr_blocks = var.private_subnet_cidrs
  }

  ingress {
    from_port   = 9113
    to_port     = 9113
    protocol    = "TCP"
    cidr_blocks = var.private_subnet_cidrs
  }

  ## outgoing: all
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }

  tags = {
    Name        = "${var.project}_${var.env}_marlowe"
    Project     = "${var.project}"
    Environment = "${var.env}"
  }
}

data "template_file" "marlowe_user_data" {
  template = "${file("${path.module}/templates/default_configuration.nix")}"

  vars = {
    root_ssh_keys      = "${join(" ", formatlist("\"%s\"", data.template_file.nixops_ssh_keys.*.rendered))}"
  }
}

resource "aws_instance" "marlowe_a" {
  ami = "${lookup(var.aws_amis, var.aws_region)}"

  instance_type        = "${var.marlowe_instance_type}"
  subnet_id            = "${aws_subnet.private.*.id[0]}"
  user_data            = "${data.template_file.marlowe_user_data.rendered}"

  vpc_security_group_ids = [
    "${aws_security_group.marlowe.id}",
  ]

  root_block_device {
    volume_size = "20"
  }

  tags = {
    Name        = "${var.project}_${var.env}_marlowe_a"
    Project     = "${var.project}"
    Environment = "${var.env}"
  }
}

resource "aws_route53_record" "marlowe_internal_a" {
  zone_id = "${aws_route53_zone.plutus_private_zone.zone_id}"
  type    = "A"
  name    = "marlowe-a.${aws_route53_zone.plutus_private_zone.name}"
  ttl     = 300
  records = ["${aws_instance.marlowe_a.private_ip}"]
}

resource "aws_instance" "marlowe_b" {
  ami = "${lookup(var.aws_amis, var.aws_region)}"

  instance_type        = "${var.marlowe_instance_type}"
  subnet_id            = "${aws_subnet.private.*.id[1]}"
  user_data            = "${data.template_file.marlowe_user_data.rendered}"

  vpc_security_group_ids = [
    "${aws_security_group.marlowe.id}",
  ]

  root_block_device {
    volume_size = "20"
  }

  tags = {
    Name        = "${var.project}_${var.env}_marlowe_b"
    Project     = "${var.project}"
    Environment = "${var.env}"
  }
}

resource "aws_route53_record" "marlowe_internal_b" {
  zone_id = "${aws_route53_zone.plutus_private_zone.zone_id}"
  type    = "A"
  name    = "marlowe-b.${aws_route53_zone.plutus_private_zone.name}"
  ttl     = 300
  records = ["${aws_instance.marlowe_b.private_ip}"]
}
