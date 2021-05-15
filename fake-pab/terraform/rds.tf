data "aws_secretsmanager_secret_version" "creds" {
  # Fill in the name you gave to your secret
  secret_id = "fake-pab/rds"
}

locals {
  db_creds = jsondecode(
    data.aws_secretsmanager_secret_version.creds.secret_string
  )
}

module "vpc" {
  source = "./vpc"

  vpc_cidr = "192.168.0.0/16"

  route = [
    {
      cidr_block     = "0.0.0.0/0"
      gateway_id     = module.vpc.gateway_id
      instance_id    = null
      nat_gateway_id = null
    }
  ]

  subnet_ids = [aws_subnet.fake-pab-subnet-a.id]
}

resource "aws_subnet" "fake-pab-subnet-a" {
  vpc_id            = module.vpc.id
  cidr_block        = "192.168.0.0/26"
  availability_zone = "eu-west-2a"
}

resource "aws_subnet" "fake-pab-subnet-b" {
  vpc_id            = module.vpc.id
  cidr_block        = "192.168.1.0/26"
  availability_zone = "eu-west-2b"
}

resource "aws_subnet" "fake-pab-subnet-c" {
  vpc_id            = module.vpc.id
  cidr_block        = "192.168.2.0/26"
  availability_zone = "eu-west-2c"
}

module "ec2" {
  source = "./ec2"

  ami           = "ami-050949f5d3aede071" # Debian 10 
  instance_type = "t2.small"
  subnet_id     = aws_subnet.fake-pab-subnet-a.id

  associate_public_ip_address = true
  vpc_security_group_ids      = [aws_security_group.fake-pab-ec2-sg.id]

  vpc_id = module.vpc.id
}

resource "aws_security_group" "fake-pab-ec2-sg" {
  name = "fake-pab-ec2-sg"

  description = "EC2 security group (terraform-managed)"
  vpc_id      = module.vpc.id

  ingress {
    from_port   = 22
    to_port     = 22
    protocol    = "tcp"
    description = "SSH"
    cidr_blocks = ["0.0.0.0/0"]
  }

  ingress {
    from_port   = 22
    to_port     = 22
    protocol    = "tcp"
    description = "SSH"
    cidr_blocks = ["0.0.0.0/0"]
  }

  ingress {
    from_port   = 80
    to_port     = 80
    protocol    = "tcp"
    description = "HTTP"
    cidr_blocks = ["192.168.0.0/16"]
  }

  ingress {
    from_port   = 5432
    to_port     = 5432
    protocol    = "tcp"
    description = "MySql"
    cidr_blocks = ["0.0.0.0/0"]
  }

  # Allow all outbound traffic.
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
}

resource "aws_db_subnet_group" "fake-pab-db-subnet-group" {
  name = "fake-pab-db-subnet-group"
  subnet_ids = [aws_subnet.fake-pab-subnet-a.id,
    aws_subnet.fake-pab-subnet-b.id,
  aws_subnet.fake-pab-subnet-c.id]

  tags = {
    Name = "fake-pab DB subnet group"
  }
}

resource "aws_rds_cluster" "fake-pab-db" {
  cluster_identifier      = "fake-pab-db-cluster"
  engine                  = "aurora-postgresql"
  availability_zones      = ["eu-west-2a", "eu-west-2b", "eu-west-2c"]
  database_name           = "fakepab"
  master_username         = local.db_creds.username
  master_password         = local.db_creds.password
  preferred_backup_window = "07:00-09:00"
  engine_mode             = "serverless"
  skip_final_snapshot     = true
  vpc_security_group_ids  = [aws_security_group.fake-pab-ec2-sg.id]
  db_subnet_group_name    = aws_db_subnet_group.fake-pab-db-subnet-group.id

  scaling_configuration {
    auto_pause               = true
    max_capacity             = 8
    min_capacity             = 2
    seconds_until_auto_pause = 300
    timeout_action           = "ForceApplyCapacityChange"
  }
}

