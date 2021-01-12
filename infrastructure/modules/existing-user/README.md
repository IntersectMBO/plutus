# Existing User Module

This module is intended to be used to bring existing AWS users into management by terraform.

## Use

Create an existing user resource:
```
module "joe_blogs" {
  source     = "../modules/existing-user"
  username   = "joe.blogs"
  policy_arn = "arn:aws:iam::aws:policy/AdministratorAccess"
}
```

Import the user components into terraform:
```
# init the module
terraform init
# import the components
sh ../modules/existing-user/import.sh joe.blogs
# check everything worked - there should be nothing for terraform to do
terraform plan
```