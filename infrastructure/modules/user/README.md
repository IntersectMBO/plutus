# Existing User Module

This module is intended to create new AWS users.

## Use

Create a new user resource:
```
module "joe_blogs" {
  source     = "../modules/user"
  username   = "joe.blogs"
  policy_arn = "arn:aws:iam::aws:policy/AdministratorAccess"
}
```

1. Ask the user to send you their gpg public key, this should be in binary format, base64 encoded: `gpg --export joeblogs | base64 > joe.blogs.base64`
2. Copy their key to `keys/joe.blogs.base64`
3. Run `terraform plan` and if everything looks good `terraform apply`
4. There should be 2 new files in the `private` directory, these are the AWS console login password and the secret for cli access, send these to the user
5. The user needs to decrypt and decode them with `base64 -d < joe.blogs.password | gpg -d` and `base64 -d < joe.blogs.secret | gpg -d`
6. Ask the user to (login to AWS console for both KEVM and IELE](https://dev-mantis.signin.aws.amazon.com/console) using the username you used in users.tf and the password you sent them
7. The user should now [set up MFA](https://docs.aws.amazon.com/IAM/latest/UserGuide/id_credentials_mfa_enable_virtual.html)
8. The user can view their AWS_ACCESS_KEY in the Summary section of their user's IAM page, see [here](https://console.aws.amazon.com/iam/home?region=eu-west-1#/users)
9. The user should add a new entry in their `~/.aws/credentials` file (figure 1)
10. The user can now run `eval $(getcreds joe.blogs 123456)` where `123456` is the MFA code provided by their MFA device
11. The user should now be able to access aws resources