
resource "aws_vpc" "fake-pab-vpc" {
  cidr_block = var.vpc_cidr

  enable_dns_support   = true
  enable_dns_hostnames = true
}

resource "aws_internet_gateway" "fake-pab-iw" {
  vpc_id = aws_vpc.fake-pab-vpc.id
}

resource "aws_route_table" "fake-pab-route-table" {
  vpc_id = aws_vpc.fake-pab-vpc.id

  dynamic "route" {
    for_each = var.route

    content {
      cidr_block     = route.value.cidr_block
      gateway_id     = route.value.gateway_id
      instance_id    = route.value.instance_id
      nat_gateway_id = route.value.nat_gateway_id
    }
  }
}

resource "aws_route_table_association" "fake-pab-vpc-route-table" {
  count = length(var.subnet_ids)

  subnet_id      = element(var.subnet_ids, count.index)
  route_table_id = aws_route_table.fake-pab-route-table.id
}

variable "vpc_cidr" {
  type = string
}

variable "route" {
  type = list(map(string))
}

variable "subnet_ids" {
  type = list(string)
}

output "id" {
  value = aws_vpc.fake-pab-vpc.id
}

output "gateway_id" {
  value = aws_internet_gateway.fake-pab-iw.id
}