# Security Group
resource "aws_security_group" "marlowe_dash" {
  vpc_id = aws_vpc.plutus.id
  name   = "${var.project}_${var.env}_marlowe_dash"

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

  ## outgoing: all
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }

  tags = {
    Name        = "${var.project}_${var.env}_marlowe_dash"
    Project     = var.project
    Environment = var.env
  }
}

data "template_file" "marlowe_dash_user_data" {
  template = file("${path.module}/templates/default_configuration.nix")

  vars = {
    root_ssh_keys      = join(" ", formatlist("\"%s\"", data.template_file.nixops_ssh_keys.*.rendered))
  }
}

module "nixos_image" {
    source  = "git::https://github.com/tweag/terraform-nixos.git//aws_image_nixos?ref=5f5a0408b299874d6a29d1271e9bffeee4c9ca71"
    release = "20.09"
}

resource "aws_instance" "marlowe_dash_a" {
  ami = module.nixos_image.ami

  instance_type        = var.marlowe_dash_instance_type
  subnet_id            = aws_subnet.private.*.id[0]
  user_data            = data.template_file.marlowe_dash_user_data.rendered

  vpc_security_group_ids = [
    aws_security_group.marlowe_dash.id,
  ]

  root_block_device {
    volume_size = "20"
  }

  tags = {
    Name        = "${var.project}_${var.env}_marlowe_dash_a"
    Project     = var.project
    Environment = var.env
  }
}

resource "aws_route53_record" "marlowe_dash_internal_a" {
  zone_id = aws_route53_zone.plutus_private_zone.zone_id
  type    = "A"
  name    = "marlowe-dash-a.${aws_route53_zone.plutus_private_zone.name}"
  ttl     = 300
  records = [aws_instance.marlowe_dash_a.private_ip]
}

resource "aws_instance" "marlowe_dash_b" {
  ami = module.nixos_image.ami

  instance_type        = var.marlowe_dash_instance_type
  subnet_id            = aws_subnet.private.*.id[1]
  user_data            = data.template_file.marlowe_dash_user_data.rendered

  vpc_security_group_ids = [
    aws_security_group.marlowe_dash.id,
  ]

  root_block_device {
    volume_size = "20"
  }

  tags = {
    Name        = "${var.project}_${var.env}_marlowe_dash_b"
    Project     = var.project
    Environment = var.env
  }
}

resource "aws_route53_record" "marlowe_dash_internal_b" {
  zone_id = aws_route53_zone.plutus_private_zone.zone_id
  type    = "A"
  name    = "marlowe-dash-b.${aws_route53_zone.plutus_private_zone.name}"
  ttl     = 300
  records = [aws_instance.marlowe_dash_b.private_ip]
}