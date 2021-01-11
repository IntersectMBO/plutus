variable "username" {}
variable "policy_arn" {}

resource "aws_iam_user" "user" {
  name = var.username
}

resource "aws_iam_user_login_profile" "user" {
  user    = aws_iam_user.user.name
  pgp_key = file("${path.root}/keys/${var.username}.base64")
}

resource "aws_iam_access_key" "user" {
  user    = aws_iam_user.user.name
  pgp_key = file("${path.root}/keys/${var.username}.base64")
}

resource "aws_iam_user_policy_attachment" "user" {
  user       = aws_iam_user.user.name
  policy_arn = var.policy_arn
}

resource "local_file" "user_password" {
  filename = "${path.root}/private/${var.username}.password"
  content  = aws_iam_user_login_profile.user.encrypted_password
}

resource "local_file" "user_secret" {
  filename = "${path.root}/private/${var.username}.secret"
  content  = aws_iam_access_key.user.encrypted_secret
}
