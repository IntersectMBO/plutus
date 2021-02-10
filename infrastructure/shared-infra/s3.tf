resource "aws_s3_bucket" "dev-mantis-users" {
  bucket = "dev-mantis-users"
  acl    = "private"

  tags = {
    Name        = "Dev Mantis Users"
  }
}