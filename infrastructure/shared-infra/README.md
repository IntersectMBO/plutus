# Shared Infrastructure

This is the place to define infrastructure that is used by all plutus deployments in the dev-mantis account. For example the continuous delivery server and S3 buckets that are not created elsewhere.

## Deployer

There is an EC2 machine that can be used to deploy other environments using morph and it also runs a grafana instance that can be used to monitor all the plutus environments. To deploy with morph you will need to add an ssh config entry to ensure that morph uses the root user:

``` 
Host deployer.goguen.monitoring.iohkdev.io
  User root
```

## Monitoring

Plutus machines can be viewed at [http://deployer.goguen.monitoring.iohkdev.io:3000/?orgId=1](http://deployer.goguen.monitoring.iohkdev.io:3000/?orgId=1)
