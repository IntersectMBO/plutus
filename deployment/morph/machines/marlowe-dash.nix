{ pkgs, config, lib, tfinfo, ... }:
{
  imports = [
    ./std.nix
    ../../../nix/modules/pab.nix
  ];

  networking = {
    firewall.allowedTCPPorts = [ 22 80 9080 ];
  };

  services.pab = {
    enable = true;
    pab-setup = pkgs.plutus-pab.pab-exes.plutus-pab-setup;
    pab-executable = "${pkgs.marlowe-pab}/bin/marlowe-pab";
    staticContent = pkgs.marlowe-dashboard.client;
    dbFile = "/var/lib/pab/pab-core.db";
    defaultWallet = 1;
    webserverPort = 9080;
    walletPort = 8081;
    nodePort = 8082;
    chainIndexPort = 8083;
    signingProcessPort = 8084;
    slotZeroTime = 1596059091000; # In milliseconds. See note [Datetime to slot] in Marlowe.Slot
    slotLength = 1000; # In milliseconds
    constantFee = 10; # Constant fee per transaction in lovelace
    scriptsFeeFactor = 0.0; # Factor by which to multiply the size-dependent scripts fee in lovelace
  };

}
