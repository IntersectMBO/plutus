module "nixos_image" {
  source  = "git::https://github.com/tweag/terraform-nixos.git//aws_image_nixos?ref=5f5a0408b299874d6a29d1271e9bffeee4c9ca71"
  release = "20.09"
}

data "template_file" "deployer_user_data" {
  template = "${file("${path.module}/templates/deployer.nix")}"

  vars = {
    root_ssh_keys = join(" ", formatlist("\"%s\"", local.root_ssh_keys))
  }
}

resource "aws_instance" "deployer" {
  ami                         = module.nixos_image.ami
  instance_type               = "t3.medium"
  associate_public_ip_address = true
  user_data                   = data.template_file.deployer_user_data.rendered
  source_dest_check           = false
  subnet_id                   = "subnet-4189951a"

  root_block_device {
    volume_size = 20
  }

  tags = {
    Name = "Plutus Deployment Machine"
  }
}

resource "aws_route53_record" "deployer" {
  zone_id = "Z2Y3TWJMJ0Q6Z7"
  type    = "A"
  name    = "deployer.goguen.monitoring.iohkdev.io"
  ttl     = 300
  records = [aws_instance.deployer.public_ip]
}
