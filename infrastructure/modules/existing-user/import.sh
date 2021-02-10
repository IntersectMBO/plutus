#!/usr/bin/env bash

# usage: sh import.sh joe.blogs
set -x
USERNAME=$1
RESOURCE=${USERNAME/./_}
touch ./keys/"$USERNAME".base64
terraform import module."$RESOURCE".aws_iam_user.user "$USERNAME"
terraform import module."$RESOURCE".aws_iam_user_policy_attachment.user "$USERNAME"/arn:aws:iam::aws:policy/AdministratorAccess
terraform import module."$RESOURCE".aws_iam_user_login_profile.user "$USERNAME"