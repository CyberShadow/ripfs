{ lib, pkgs, ripfs }:

pkgs.testers.nixosTest {
  name = "ripfs-integration";

  nodes.machine = { config, pkgs, ... }: {
    environment.systemPackages = [ ripfs ];

    # Ensure FUSE is available
    boot.kernelModules = [ "fuse" ];

    # Mount as an unprivileged user, through the setuid fusermount3.
    users.users.alice = {
      isNormalUser = true;
    };
    programs.fuse.enable = true;

    virtualisation = {
      memorySize = 1024;
    };
  };

  testScript = builtins.readFile ./test_script.py;
}
