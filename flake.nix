{
  description = "ripfs - deduplicating userspace filesystem for Internet radio recordings";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # Filter source to only include files needed for building
        ripfsSrc = pkgs.lib.cleanSourceWith {
          src = ./.;
          filter = path: type:
            let
              baseName = baseNameOf path;
            in
              baseName == "ripfs.d" ||
              baseName == "dub.sdl" ||
              baseName == "dub.selections.json";
        };

        ripfs = pkgs.buildDubPackage {
          pname = "ripfs";
          version = "0.1.0";

          src = ripfsSrc;

          dubLock = ./dub-lock.json;

          buildInputs = with pkgs; [
            fuse3
          ];

          nativeBuildInputs = with pkgs; [
            pkg-config
          ];

          # oxfuse's preGenerateCommands runs a script with a #!/bin/bash
          # shebang.
          postConfigure = ''
            patchShebangs --build "$DUB_HOME"/packages/oxfuse
          '';

          installPhase = ''
            runHook preInstall
            install -Dm755 ripfs -t $out/bin
            runHook postInstall
          '';

          meta = with pkgs.lib; {
            description = "Deduplicating userspace filesystem for Internet radio recordings";
            license = licenses.mpl20;
            platforms = platforms.linux;
            mainProgram = "ripfs";
          };
        };
      in
      {
        packages = {
          default = ripfs;
          ripfs = ripfs;
        };

        apps.default = {
          type = "app";
          program = "${ripfs}/bin/ripfs";
        };

        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            ldc
            dub
            fuse3
            pkg-config
          ];
        };

        # Integration tests (only on Linux, requires VM)
        checks = pkgs.lib.optionalAttrs pkgs.stdenv.isLinux {
          integration = import ./ci/tests/nixos-test.nix {
            inherit (pkgs) lib;
            inherit pkgs;
            inherit ripfs;
          };
        };
      }
    );
}
