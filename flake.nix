{
  description = "Cubical Agda library for categorical logic and type theory";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    agda.url = "github:agda/agda";
    cubical = {
      url = "github:agda/cubical";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "flake-utils";
        agda.follows = "agda";
      };
    };
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
    cubical,
    ...
  }:
    let
      overlay = final: prev: {
        cubical-categorical-logic = final.agdaPackages.mkDerivation {
          pname = "cubical-categorical-logic";
          version = "0.1";

          src = final.lib.cleanSourceWith {
            filter = name: _type:
              !(final.lib.hasSuffix ".nix" name)
              && !(final.lib.hasSuffix "flake.lock" name)
              && !(final.lib.hasSuffix ".envrc" name);
            src = final.lib.cleanSource ./.;
          };

          LC_ALL = "C.UTF-8";

          # Use the cubical-overlay's agdaWithCubical wrapper. agda
          # reads cubical's cached .agdai files straight out of the
          # /nix/store read-only; as long as our flag set doesn't
          # force a recheck of any cubical file, this works without
          # copying cubical into the sandbox.
          nativeBuildInputs = [ final.agdaWithCubical ];

          buildPhase = ''
            runHook preBuild
            make check
            runHook postBuild
          '';

          meta = {
            description = "Cubical Agda library for categorical logic and type theory";
          };
        };

        agdaWithCubicalCategoricalLogic =
          final.agdaPackages.agda.withPackages [
            final.cubical
            final.cubical-categorical-logic
          ];
      };

      overlays = [
        cubical.inputs.agda.overlays.default
        cubical.overlays.default
        overlay
      ];
    in
    { overlays.default = overlay; } //
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system overlays; };
      in
      {
        packages = {
          inherit (pkgs) cubical-categorical-logic agdaWithCubicalCategoricalLogic;
          default = pkgs.cubical-categorical-logic;
        };

        # Development shell: pinned Agda + cubical library and
        # fix-whitespace. Activate via `nix develop` or direnv.
        #
        # To use a local cubical checkout:
        #   nix develop --override-input cubical path:../Cubical
        devShells.default = pkgs.mkShell {
          nativeBuildInputs = [
            pkgs.agdaWithCubical
            pkgs.haskellPackages.fix-whitespace
          ];
        };
      }
    );
}
