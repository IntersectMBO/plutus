# Security Group
resource "aws_security_group" "prometheus" {
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

  # prometheus server port
  ingress {
    from_port   = local.prometheus_port
    to_port     = local.prometheus_port
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
    Name        = "${local.project}_${var.env}_prometheus"
    Project     = local.project
    Environment = var.env
  }
}

data "template_file" "prometheus_user_data" {
  template = "${file("${path.module}/templates/prometheus_configuration.nix")}"

  vars = {
    ssh_keys      = "${join(" ", formatlist("\"%s\"", local.root_ssh_keys))}"
  }
}

resource "aws_instance" "prometheus" {
  ami           = module.nixos_image.ami
  instance_type = var.prometheus_instance_type
  subnet_id     = aws_subnet.private.*.id[0]
  user_data     = data.template_file.prometheus_user_data.rendered

  vpc_security_group_ids = [
    aws_security_group.prometheus.id,
  ]

  root_block_device {
    volume_size = 100
  }

  tags = {
    Name        = "${local.project}_${var.env}_prometheus"
    Project     = local.project
    Environment = var.env
  }
}

resource "aws_route53_record" "prometheus" {
  zone_id = aws_route53_zone.plutus_private_zone.zone_id
  type    = "A"
  name    = "prometheus.${aws_route53_zone.plutus_private_zone.name}"
  ttl     = 300
  records = [aws_instance.prometheus.private_ip]
}
