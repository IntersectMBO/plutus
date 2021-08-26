{
  services.nomad.client.host_volume = [{
    pab = {
      path = "/var/lib/nomad-volumes/pab";
      read_only = false;
    };
  }];

  system.activationScripts.nomad-host-volumes = ''
    mkdir -p /var/lib/nomad-volumes/pab
    chown nobody:nogroup /var/lib/nomad-volumes/pab
  '';
}
