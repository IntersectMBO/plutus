resource "aws_secretsmanager_secret" "server" {
  for_each = toset(["alpha", "kris", "david", "pablo"])
  name = "server-${each.key}"
}

# When creating the new lambda we will need to add the following IAM policy
# {
#     "Version": "2012-10-17",
#     "Statement": {
#         "Effect": "Allow",
#         "Action": "secretsmanager:GetSecretValue",
#         "Resource": ${aws_secretsmanager_secret.server["david"].arn}
#     }
# }
# Secrets can be accessed using http://hackage.haskell.org/package/amazonka-secretsmanager-1.6.1/docs/Network-AWS-SecretsManager.html