{ writeShellScriptBin, gawk, awscli }:

# aws-mfa-login: Log in to aws using MFA
#```
# $ eval $(aws-mfa-login <username> <mfa-code>)
#```
writeShellScriptBin "aws-mfa-login" ''
  set -eou pipefail

  if [[ $# -ne 2 ]]; then
    echo "Please call the script with your AWS account username followed by the MFA code"
    exit 1
  fi
  export AWS_PROFILE=dev-mantis
  unset AWS_SESSION_TOKEN
  unset AWS_SECRET_ACCESS_KEY
  unset AWS_ACCESS_KEY_ID

  ${awscli}/bin/aws sts get-session-token --serial-number "arn:aws:iam::454236594309:mfa/$1" --output text --duration-seconds 86400 --token-code "$2" \
          | awk '{printf("export AWS_ACCESS_KEY_ID=%s\nexport AWS_SECRET_ACCESS_KEY=\"%s\"\nexport AWS_SESSION_TOKEN=\"%s\"\n",$2,$4,$5)}'
''
