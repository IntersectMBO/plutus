# Bootstrapping a Bitte Cluster

## Resource Preparation

* Determine whether the root AWS account, an existing organization under the root account, or a new organization will be used to host the new cluster infrastructure (3 or 5 core nodes plus a monitoring node).  Create a new organization if needed.  Switch to the desired AWS account or organization before continuing.

* Choose a target region which the infrastructure will be deployed to.  This selected region should be used for KMS, S3 and AMI resource preparation

### IAM Preparation
* Ensure users who will be admins have IAM accounts created and are assigned a group with the admin policy and programmatic access

### KMS Preparation
* If a suitable KMS key does not already exist in the selected region, create a new one:
  * Create a customer managed symmetric KMS key (no advanced options or tags required)
* Add the IAM admins and organization role to the KMS key and KMS key usage permissions
* Make note of the full KMS key ARN (`arn:aws:kms:$REGION:$ORG_ID:key/$KEY_ID`)

### S3 Preparation
* If a suitable S3 bucket does not already exist in the selected region, create a new bucket for the cluster
* Ensure that the bucket has public access BLOCKED (NO public access)

### Route53 Domain and DNS Preparation
* Select an existing domain to host the new infra or create a new one.
* To create a new one, one approach if using an organization under a parent organization or the root account which hosts the main DNS zone:
  * Create a new hosted zone in the selected organization which is a sub-domain of a parent organization or root account hosted zone
  * Create an NS record in the parent account pointing to the selected organizations new hosted zone sub-domain NS records

### AMI preparation
* Ensure that a bitte AMI image is available in the selected region
  * If not, copy an available bitte AMI image from another region to the selected region using the EC2 dashboard
  * Switch to the owner account/org of the existing AMI image, if needed, to perform the copy operation
  * The owner of the existing AMI from an originating region can be found by looking at the 12 digits of the backing snapshot
  * Those 12 digits can be used to filter organizations from the "My Organizations" page to locate the AMI owner organization
  * By switching to the owner organization, the AMI can then be copied to a target region without permission errors
  * TODO: document creation of a new AMI image from ops-lib
* Make note of the AMI ID in the selected region

## Standing up the cluster:

### Cluster setup

* Ensure that s3 credentials are set up in `~/.aws/credentials` file for the cluster
  * For systems with nix-daemon, a `/root/.aws/credentials` file may also be required for builds with s3 cache access
  * Optional: Add the cluster s3 bucket to the nix cache
    * A parameter of profile can be appended to the cache string to specify the AWS credentials profile to use (`&profile=$PROFILE`)

* Create a new terraform cloud organization for the cluster
  * Invite other members for the cluster
  * Default settings for the organization are ok are we don't manage source in the cloud

* Create a new repo (ex: infra-ops)
* Copy over skeleton files from a skeleton dir or existing bitte job repo
  * The `encrypted/` and `jobs/` folders should be deleted from any copied skeleton setup as they will be recreated

* In the `clusters/` dir, move the two sub-directories to appropriate names for the new repo, example:
  * `clusters/infra/production/`

* Update the `default.nix` file in the clusters sub-directory, `clusters/infra/production/default.nix` in this example:
  * Add additional `amis` region attributes for auto-scaling instances if needed
  * Update the `kms` key with the full ARN path
  * Update the `domain` with the domain for the new cluster
  * Update the `s3Bucket` name with the s3 bucket for the new cluster
  * Update the `adminNames` with admins that exist for the new cluster
  * Update the `terraformOrganization` to the new organization for the cluster
  * Update the `autoscalingGroups` with new regions and desired capacities as needed
    * Note: regions with less than 3 AZs are not yet supported

* Make the initial encrypted `nix-public-key-file`, `secrets/` and `encrypted/` dirs for the repo with:
```
make secrets/nix-public-key-file
```

* Add all new files (locally) to the git repo.  This is required for nix flakes to recognize files
  * Following files and directories do not need to be added:
    * `.direnv/`
    * `cert.config`
    * `config.tf.json`

* Initialize the network config for the new cluster which will create a new `config.tf.json` file:
```
nix run .#clusters.infra-production.tf.network.config
```

* Deploy the terraform network with:
```
bitte terraform network
```

* Deploy the terraform core nodes with:
```
bitte terraform core
```

* Generate the certs for the new cluster with:
```
bitte certs --domain $DOMAIN
```

* Deploy the terraform clients with:
```
bitte terraform clients
```

* Troubleshooting:
  * If nix fails due to missing files, check if new files were generated that need to be added for nix flakes to recognize them
  * If consul services, such as nomad, fail on the new core nodes, try restarting the failed services

## Cluster Jobs:

* Nomad job definitions exist in the `jobs/` folder
* Other Bitte cluster repos and their job definitions can be used as templates for new jobs
