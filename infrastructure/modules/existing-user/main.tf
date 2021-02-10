variable "username" {}
variable "policy_arn" {}

resource "aws_iam_user" "user" {
  name = var.username
}

resource "aws_iam_user_login_profile" "user" {
  user    = aws_iam_user.user.name
  pgp_key = file("${path.root}/keys/${var.username}.base64")
  lifecycle {
    ignore_changes = [
      password_length,
      password_reset_required,
      pgp_key,
    ]
  }
}

resource "aws_iam_user_policy_attachment" "user" {
  user       = aws_iam_user.user.name
  policy_arn = var.policy_arn
}