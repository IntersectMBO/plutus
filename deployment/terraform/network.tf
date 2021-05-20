# This file sets up a basic network with private and public subnets and bastion machines to enable ssh access to the private subnets

# VPC
resource "aws_vpc" "plutus" {
  cidr_block           = var.vpc_cidr
  enable_dns_hostnames = true

  tags = {
    Name        = "${local.project}_${var.env}"
    Project     = local.project
    Environment = var.env
  }
}

# Public Subnets
resource "aws_subnet" "public" {
  vpc_id            = aws_vpc.plutus.id
  availability_zone = "${var.aws_region}${var.azs[count.index]}"
  cidr_block        = var.public_subnet_cidrs[count.index]
  count             = length(var.azs)

  map_public_ip_on_launch = true

  tags = {
    Name        = "${local.project}_${var.env}_public_${var.azs[count.index]}"
    Project     = local.project
    Environment = var.env
  }
}

# Internet Gateway
resource "aws_internet_gateway" "plutus" {
  vpc_id = aws_vpc.plutus.id

  tags = {
    Name        = "${local.project}_${var.env}"
    Project     = local.project
    Environment = var.env
  }
}

# Public Route
resource "aws_route" "public" {
  route_table_id         = aws_vpc.plutus.main_route_table_id
  destination_cidr_block = "0.0.0.0/0"
  gateway_id             = aws_internet_gateway.plutus.id
}

# Elastic IPs
resource "aws_eip" "nat" {
  vpc        = true
  depends_on = [aws_internet_gateway.plutus]
  count      = length(var.azs)

  tags = {
    Name        = "${local.project}_${var.env}_${var.azs[count.index]}"
    Project     = local.project
    Environment = var.env
  }
}

# NATs
resource "aws_nat_gateway" "plutus" {
  count         = length(var.azs)
  allocation_id = aws_eip.nat.*.id[count.index]
  subnet_id     = aws_subnet.public.*.id[count.index]
  depends_on    = [aws_internet_gateway.plutus]

  tags = {
    Name        = "${local.project}_${var.env}_${var.azs[count.index]}"
    Project     = local.project
    Environment = var.env
  }
}

# Associate public subnets to public route tables
resource "aws_route_table_association" "public" {
  count          = length(var.azs)
  subnet_id      = aws_subnet.public.*.id[count.index]
  route_table_id = aws_vpc.plutus.main_route_table_id
}

# Private Subnets
resource "aws_subnet" "private" {
  count             = length(var.azs)
  vpc_id            = aws_vpc.plutus.id
  availability_zone = "${var.aws_region}${var.azs[count.index]}"
  cidr_block        = var.private_subnet_cidrs[count.index]

  tags = {
    Name        = "${local.project}_${var.env}_private_${var.azs[count.index]}"
    Project     = local.project
    Environment = var.env
  }
}

# Private Route Tables
resource "aws_route_table" "private" {
  count  = length(var.azs)
  vpc_id = aws_vpc.plutus.id

  tags = {
    Name        = "${local.project}_${var.env}_private_${var.azs[count.index]}"
    Project     = local.project
    Environment = var.env
  }
}

# Private Routes
resource "aws_route" "private" {
  count                  = length(var.azs)
  route_table_id         = aws_route_table.private.*.id[count.index]
  destination_cidr_block = "0.0.0.0/0"
  nat_gateway_id         = aws_nat_gateway.plutus.*.id[count.index]
}

# Associate private subnets to private route tables
resource "aws_route_table_association" "private" {
  count          = length(var.azs)
  subnet_id      = aws_subnet.private.*.id[count.index]
  route_table_id = aws_route_table.private.*.id[count.index]
}


resource "aws_instance" "bastion" {
  count                       = length(var.azs)
  ami                         = module.nixos_image.ami
  instance_type               = var.bastion_instance_type
  associate_public_ip_address = true
  user_data                   = data.template_file.bastion_user_data.rendered
  source_dest_check           = false

  vpc_security_group_ids = [
    "${aws_security_group.bastion.id}",
  ]

  subnet_id = aws_subnet.public.*.id[count.index]

  root_block_device {
    volume_size = 20
  }

  tags = {
    Name        = "${local.project}_${var.env}_bastion_${var.azs[count.index]}"
    Project     = local.project
    Environment = var.env
  }
}

resource "aws_security_group" "bastion" {
  vpc_id = aws_vpc.plutus.id

  # inbound (world): ICMP 3:4 "Fragmentation Needed and Don't Fragment was Set"
  ingress {
    from_port   = "3"
    to_port     = "4"
    protocol    = "ICMP"
    cidr_blocks = ["0.0.0.0/0"]
  }

  ## inbound ssh
  # We want to lock this down to the zerotier network in the future
  ingress {
    protocol    = "TCP"
    from_port   = 22
    to_port     = 22
    cidr_blocks = ["0.0.0.0/0"]
  }

  ## FIXME: We are not using zerotier now, I think we can remove this
  ## zerotier must use some custom protocol, TCP + UDP doesn't work
  # Currently asking zerotier if I can lock this down further
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }

  egress {
    from_port   = 22
    to_port     = 22
    protocol    = "TCP"
    cidr_blocks = var.private_subnet_cidrs
  }

  # Allow internet access to install things, we could maybe lock this down to nixpkgs somehow
  # These are currently a bit useless since we are letting all traffic out due to zerotier
  # but hopefully in the future we can lock things down further
  egress {
    from_port   = 80
    to_port     = 80
    protocol    = "TCP"
    cidr_blocks = ["0.0.0.0/0"]
  }

  egress {
    from_port   = 443
    to_port     = 443
    protocol    = "TCP"
    cidr_blocks = ["0.0.0.0/0"]
  }

  tags = {
    Name        = "${local.project}_${var.env}_bastion"
    Project     = local.project
    Environment = var.env
  }
}

resource "aws_route53_zone" "plutus_private_zone" {
  vpc {
    vpc_id = aws_vpc.plutus.id
  }
  name = "internal.${var.env}.${var.plutus_tld}"

  tags = {
    Name        = "${local.project}_${var.env}"
    Project     = local.project
    Environment = var.env
  }
}

resource "aws_route53_zone" "marlowe_finance_io_zone" {
  count = (var.env == "production" ? 1 : 0)
  name  = "marlowe-finance.io"
}

resource "aws_route53_record" "marlowe_finance_top_level" {
  count   = (var.env == "production" ? 1 : 0)
  zone_id = aws_route53_zone.marlowe_finance_io_zone[0].zone_id
  name    = "marlowe-finance.io"
  type    = "A"
  ttl     = 300
  records = [var.marlowe_finance_production_ip]
}

resource "aws_route53_record" "marlowe_finance_play" {
  count   = (var.env == "production" ? 1 : 0)
  zone_id = aws_route53_zone.marlowe_finance_io_zone[0].zone_id
  name    = "play.marlowe-finance.io"
  type    = "CNAME"
  ttl     = 300
  records = ["production.marlowe.iohkdev.io"]
}

resource "aws_route53_record" "marlowe_finance_run" {
  count   = (var.env == "production" ? 1 : 0)
  zone_id = aws_route53_zone.marlowe_finance_io_zone[0].zone_id
  name    = "run.marlowe-finance.io"
  type    = "CNAME"
  ttl     = 300
  records = ["production.marlowe-dash.iohkdev.io"]
}

resource "aws_route53_record" "marlowe_finance_webinar" {
  count   = (var.env == "production" ? 1 : 0)
  zone_id = aws_route53_zone.marlowe_finance_io_zone[0].zone_id
  name    = "webinar.marlowe-finance.io"
  type    = "CNAME"
  ttl     = 300
  records = ["wy8k2fnarz0v.wpeproxy.com"]
}

# Bastion hosts
data "template_file" "bastion_user_data" {
  template = "${file("${path.module}/templates/bastion_configuration.nix")}"

  vars = {
    ssh_keys   = "${join(" ", formatlist("\"command=\\\"echo 'this host is for forwarding only'\\\",no-X11-forwarding,no-user-rc %s\"", local.bastion_ssh_keys))}"
    network_id = "canbeanything"
  }
}

