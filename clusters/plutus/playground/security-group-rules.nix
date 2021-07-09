{ pkgs, lib, config, ... }:
let
  inherit (pkgs.terralib) cidrsOf;
  inherit (config.cluster.vpc) subnets;
  vpcs = pkgs.terralib.vpcs config.cluster;

  global = [ "0.0.0.0/0" ];
  internal = [ config.cluster.vpc.cidr ] ++ (lib.forEach vpcs (vpc: vpc.cidr));
in {
  # TODO: derive needed security groups from networking.firewall?
  securityGroupRules = {
    internet = {
      type = "egress";
      port = 0;
      protocols = [ "-1" ];
      cidrs = global;
    };

    internal = {
      type = "ingress";
      port = 0;
      protocols = [ "-1" ];
      cidrs = internal;
    };

    ssh = {
      port = 22;
      cidrs = global;
    };

    http = {
      port = 80;
      cidrs = global;
    };

    https = {
      port = 443;
      cidrs = global;
    };

    grpc = {
      port = 4422;
      cidrs = global;
    };

    haproxyStats = {
      port = 1936;
      cidrs = global;
    };

    vault-http = {
      port = 8200;
      cidrs = global;
    };

    consul-serf-lan = {
      port = 8301;
      protocols = [ "tcp" "udp" ];
      self = true;
      cidrs = internal;
    };

    consul-serf-wan = {
      port = 8302;
      protocols = [ "udp" ];
      self = true;
      cidrs = internal;
    };

    consul-grpc = {
      port = 8502;
      protocols = [ "tcp" "udp" ];
      cidrs = internal;
    };

    nomad-serf-lan = {
      port = 4648;
      protocols = [ "tcp" "udp" ];
      cidrs = internal;
    };

    nomad-rpc = {
      port = 4647;
      cidrs = internal;
    };

    nomad-http = {
      port = 4646;
      cidrs = internal;
    };

    routing = {
      from = 10000;
      to = 20000;
      protocols = [ "tcp" "udp" ];
      cidrs = global;
    };

  };
}
