locals {
  nixops_nginx_port = "80"
}

# Security Group
resource "aws_security_group" "nixops" {
  vpc_id = aws_vpc.plutus.id

  ## inbound (world): ICMP 3:4 "Fragmentation Needed and Don't Fragment was Set"
  ingress {
    from_port   = "3"
    to_port     = "4"
    protocol    = "ICMP"
    cidr_blocks = ["0.0.0.0/0"]
  }

  ## inbound (world): ssh
  ingress {
    from_port   = 22
    to_port     = 22
    protocol    = "TCP"
    cidr_blocks = var.public_subnet_cidrs
  }

  ingress {
    from_port   = local.nixops_nginx_port
    to_port     = local.nixops_nginx_port
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
    Name        = "${var.project}_${var.env}_nixops"
    Project     = var.project
    Environment = var.env
  }
}

data "template_file" "nixops_ssh_keys" {
  template = "$${ssh_key}"
  count    = length(var.nixops_ssh_keys[var.env])

  vars = {
    ssh_key = "${var.ssh_keys["${element(var.nixops_ssh_keys["${var.env}"], count.index)}"]}"
  }
}

data "template_file" "nixops_user_data" {
  template = "${file("${path.module}/templates/nixops_configuration.nix")}"

  vars = {
    ssh_keys      = "${join(" ", formatlist("\"%s\"", data.template_file.nixops_ssh_keys.*.rendered))}"
  }
}

resource "aws_instance" "nixops" {
  ami           = lookup(var.aws_amis, var.aws_region)
  instance_type = var.nixops_instance_type
  subnet_id     = aws_subnet.private.*.id[0]
  user_data     = data.template_file.nixops_user_data.rendered

  vpc_security_group_ids = [
    aws_security_group.nixops.id,
  ]

  root_block_device {
    volume_size = 100
  }

  tags = {
    Name        = "${var.project}_${var.env}_nixops"
    Project     = var.project
    Environment = var.env
  }
}

resource "aws_route53_record" "nixops" {
  zone_id = aws_route53_zone.plutus_private_zone.zone_id
  type    = "A"
  name    = "nixops.${aws_route53_zone.plutus_private_zone.name}"
  ttl     = 300
  records = [aws_instance.nixops.private_ip]
}
