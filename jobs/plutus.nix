{ mkNomadJob, systemdSandbox, writeShellScript, coreutils, lib
, cacert, curl, dnsutils, gawk, gnugrep, iproute, jq
, lsof, netcat, nettools, procps, telegraf
, remarshal, dockerImages }:
let
  namespace = "plutus-dev";

  mkPlutus = { index, requiredPeerCount, public ? false }:
    let
      localRpcPort = (if public then 10000 else 7000) + index;
      localRestPort = (if public then 11000 else 9000) + index;
      localPrometheusPort = 10000 + index;
      publicPort = 7100 + index;

      name = if public then
        "follower-${toString index}"
      else
        "leader-${toString index}";
    in {
      ${name} = {
        count = 1;

        volumes.${name} = {
          type = "host";
          source = "plutus-playground";
        };

        networks = [{
          ports = {
            prometheus.to = 7000;
            rest.to = localRestPort;
            rpc.to = localRpcPort;
          };
        }];

        services."${namespace}-${name}-monitor" = {
          portLabel = "prometheus";
          task = "monitor";
        };

        tasks.monitor = {
          driver = "docker";

          resources = {
            cpu = 100; # mhz
            memoryMB = 256;
          };

          config = {
            image = dockerImages.monitor.id;
            ports = [ "prometheus" ];
            labels = [{
              inherit namespace name;
              imageTag = dockerImages.monitor.image.imageTag;
            }];

            logging = {
              type = "journald";
              config = [{
                tag = "${name}-monitor";
                labels = "name,namespace,imageTag";
              }];
            };
          };
        };

        tasks.env = {
          driver = "docker";
          config.image = dockerImages.env.id;
          resources = {
            cpu = 10; # mhz
            memoryMB = 10;
          };
        };

        tasks.telegraf = {
          driver = "docker";

          vault.policies = [ "nomad-cluster" ];

          resources = {
            cpu = 100; # mhz
            memoryMB = 128;
          };

          config = {
            image = dockerImages.telegraf.id;
            args = [ "-config" "local/telegraf.config" ];
            labels = [{
              inherit namespace name;
              imageTag = dockerImages.telegraf.image.imageTag;
            }];

            logging = {
              type = "journald";
              config = [{
                tag = "${name}-telegraf";
                labels = "name,namespace,imageTag";
              }];
            };
          };

          templates = [{
            data = ''
              [agent]
              flush_interval = "10s"
              interval = "10s"
              omit_hostname = false

              [global_tags]
              client_id = "${name}"
              namespace = "${namespace}"

              [inputs.prometheus]
              metric_version = 1

              urls = [ "http://{{ env "NOMAD_ADDR_prometheus" }}" ]

              [outputs.influxdb]
              database = "telegraf"
              urls = ["http://{{with node "monitoring" }}{{ .Node.Address }}{{ end }}:8428"]
            '';

            destination = "local/telegraf.config";
          }];
        };
      };
    };
in {
  ${namespace} = mkNomadJob "plutus" {
    datacenters = [ "eu-central-1" "us-east-2" ];
    type = "service";
    inherit namespace;

    # update = {
    #   maxParallel = 1;
    #   healthCheck = "checks";
    #   minHealthyTime = "1m";
    #   healthyDeadline = "5m";
    #   progressDeadline = "10m";
    #   autoRevert = true;
    #   autoPromote = true;
    #   canary = 1;
    #   stagger = "1m";
    # };

    taskGroups = (mkPlutus {
      index = 0;
      public = false;
      requiredPeerCount = 0;
    }) // (mkPlutus {
      index = 1;
      public = false;
      requiredPeerCount = 1;
    }) // (mkPlutus {
      index = 2;
      public = false;
      requiredPeerCount = 2;
    }) // (mkPlutus {
      index = 0;
      public = true;
      requiredPeerCount = 3;
    });
  };
}
