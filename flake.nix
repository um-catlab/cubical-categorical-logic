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
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            cubical.inputs.agda.overlays.default
            cubical.overlays.default
          ];
        };

      in
      {
        packages.default = pkgs.agdaPackages.mkDerivation {
          pname = "cubical-categorical-logic";
          version = "0.1";

          src = pkgs.lib.cleanSourceWith {
            filter = name: _type:
              !(pkgs.lib.hasSuffix ".nix" name)
              && !(pkgs.lib.hasSuffix "flake.lock" name)
              && !(pkgs.lib.hasSuffix ".envrc" name);
            src = pkgs.lib.cleanSource ./.;
          };

          nativeBuildInputs = [ pkgs.ghc ];
          buildInputs = [ pkgs.cubical ];

          buildPhase = ''
            runHook preBuild
            runhaskell ./Everythings.hs gen-except
            agda -W error +RTS -M8G -RTS TestEverything.agda
            runHook postBuild
          '';

          meta = {
            description = "Cubical Agda library for categorical logic and type theory";
          };
        };

        # Development shell: pinned Agda + cubical library, GHC, and
        # fix-whitespace. Activate via `nix develop` or direnv.
        #
        # To use a local cubical checkout:
        #   nix develop --override-input cubical path:../Cubical
        devShells.default = pkgs.mkShell {
          nativeBuildInputs = [
            pkgs.agdaWithCubical
            pkgs.ghc
            pkgs.haskellPackages.fix-whitespace
          ];
        };
      }
    );
}
