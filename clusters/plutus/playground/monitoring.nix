{ ... }: {
  services.telegraf.extraConfig.inputs = {
    statsd = {
      protocol = "udp";
      service_address = ":8125";
      delete_gauges = true;
      delete_counters = true;
      delete_sets = true;
      delete_timings = true;
      percentiles = [ 90 ];
      metric_separator = "_";
      datadog_extensions = true;
      allowed_pending_messages = 10000;
      percentile_limit = 1000;
    };

    prometheus = {
      urls = [ "http://127.0.0.1:3101/metrics" "http://127.0.0.1:13798/" ];
      metric_version = 1;
    };

    cpu = {
      percpu = true;
      totalcpu = true;
      collect_cpu_time = false;
    };

    disk = { };

    diskio = { };

    systemd_units = { unittype = "service"; };

    x509_cert = { sources = [ "/etc/ssl/certs/cert.pem" ]; };

    kernel = { };
    linux_sysctl_fs = { };
    mem = { };
    net = { interfaces = [ "en*" ]; };
    netstat = { };
    processes = { };
    swap = { };
    system = { };
    procstat = { pattern = "(consul)"; };
    consul = {
      address = "localhost:8500";
      scheme = "http";
    };
  };
}
