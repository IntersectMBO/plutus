# Existing User Module

This module is intended to create new AWS users.

## How to create new users

To create a new account, the new user has to follow through the instructions in sections 1 and 2 below. Then an existing user with admin rights has to follow through the instructions in section 3. The new user should then be able to get access to AWS using the instrutions in section 4.

### 1. New user: Create a GPG public key

If you already have a GPG pubic key, skip straight to the next section.

1. Install GPG if you don't have it (e.g. `brew install gnupg` on MacOS or `apt-get install gnupg` on Ubuntu).
2. Create a GPG public key: `gpg --full-generate-key`. All the default options are fine. At the end you should see something like this:
    ```
    pub   rsa3072 yyyy-mm-dd [SC]
          XXXXXXXXXX
    uid           [ultimate] Joe Bloggs <joe@bloggs.com>
    sub   rsa3072 yyyy-mm-dd [E]
    ```
3. Make a note of the key label `XXXXXXXXXX`. You can see it again using `gpg -k`.

### 2. New user: Add your public key to a new branch

1. Create and checkout a new branch, e.g. `add-joe-to-aws`.
2. `cd infrastructure/aws-accounts/keys`.
3. Export your GPG public key to `joe.bloggs.base64`: `gpg --export XXXXXXXXXX | base64 > joe.blogs.base64`.
4. Create a new user resource in `infrastructure/aws-accounts/users.tf`:
    ```
    module "joe_blogs" {
      source     = "../modules/user"
      username   = "joe.blogs"
      policy_arn = "arn:aws:iam::aws:policy/AdministratorAccess"
    }
    ```
5. Commit these files to your branch and push.

### 3. Existing user: Terraform

1. Checkout `add-joe-to-aws`.
2. Run `terraform plan` and if everything looks good `terraform apply`.
3. There should be 2 new files in the `infrastructure/aws-accounts/private` directory. These are the AWS console login password and the secret for cli access. Commit these files and push.

### 4. New user: Get access to AWS

1. `cd ../private`.
2. `git pull` (to get the 2 new files just mentioned).
3. You now need to decrypt and decode these files with `base64 -d < joe.blogs.password | gpg -d` and `base64 -d < joe.blogs.secret | gpg -d`. Make a note of the results.
4. [Login to AWS console](https://dev-mantis.signin.aws.amazon.com/console) using the username you used in `infrastructure/aws-accounts/users.tf` and the password you decrypted from `joe.blogs.password`. You will be prompted to set a new password.
5. Follow the instructions to [set up MFA](https://docs.aws.amazon.com/IAM/latest/UserGuide/id_credentials_mfa_enable_virtual.html) on your AWS account.
6. Make a note of your Access key ID. It is displayed under your Security credentials tab in the Summary section of your IAM page.
7. From inside your nix-shell, run `aws configure`. At the prompts, enter the following:
    - AWS Access key ID: your Access key ID from step 6.
    - AWS Secret Access Key: the key you decoded from `joe.bloggs.secret` at step 3.
    - Default region name: `eu-west-1`.
    - Default output format: leave blank.
8. Edit `~/.aws/credentials` and `~/.aws/config` replacing `[default]` with `[dev-mantis]` in both of them.
9. You should now be able to run `eval $(getcreds joe.blogs 123456)` where `123456` is the MFA code provided by your MFA device. This will export the necessary AWS env variables.
10. You should now be able to access AWS resources. :tada:

### 5. And finally...

Someone needs to merge `add-joe-to-aws` to `master`.
