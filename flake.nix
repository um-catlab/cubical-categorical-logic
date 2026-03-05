# Based off of flake at
# https://github.com/phijor/cubical-containers/blob/04a2287401da2a07d7763f2deb684def3a881791/flake.nix
# with modifications from Cass Alexandru (cxandru)
{
  description = "Cubical categorical logic library for Agda";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    cubical = {
      url = "github:agda/cubical";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "flake-utils";
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
      inherit (flake-utils.lib) eachDefaultSystem;
    in
    eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ cubical.overlays.default ];
        };

        cubical-categorical-logic = pkgs.agdaPackages.mkDerivation {
          pname = "cubical-categorical-logic";
          version = "0.9";

          src = ./.;

          nativeBuildInputs = [ pkgs.ghc ];
          buildInputs = [ pkgs.cubical ];

          preConfigure = ''
            make build
            make clean-everythings
            rm TestEverything.agda
          '';

          meta = {
            description = "Extensions to the cubical stdlib category theory for categorical logic/type theory";
            platforms = pkgs.lib.platforms.all;
          };
        };
      in
      {
        packages.default = cubical-categorical-logic;
        devShells.default = pkgs.mkShell {
          inputsFrom = [ cubical-categorical-logic ];
        };
      }
    );
}
