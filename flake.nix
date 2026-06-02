{
  description = "Cubical Agda library for categorical logic and type theory (built with Mikan)";

  inputs = {
    # Match Mikan's nixpkgs so we share the stdenv that Mikan was built against.
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
    flake-utils.url = "github:numtide/flake-utils";

    # Mikan is 1lab's fork of Agda. It is a (mostly) drop-in replacement for
    # cubical Agda: same `.agda-lib`/`AGDA_DIR`/`libraries` machinery, same
    # `--build-library`/`--library-file` flags. The only user-visible
    # difference is that the executable is called `mikan`, not `agda`.
    # See https://codeberg.org/1lab/mikan
    mikan.url = "git+https://codeberg.org/1lab/mikan?ref=main";

    # The "deployed" cubical: a Mikan-built copy, type-checked once and pinned
    # in flake.lock. The `default` dev shell / `cubical` package use this, and
    # because it is pinned it does NOT rebuild while you work on this library.
    # Re-snapshot it with `nix flake update cubical`.
    #
    # NB: deliberately NOT `follows`-ing nixpkgs/mikan here. Letting cubical use
    # its own pinned inputs means ccl consumes cubical's *already-built* store
    # output as-is, instead of re-deriving (and re-type-checking!) cubical under
    # ccl's nixpkgs. ccl's own `mikan` input tracks the same `main`, so the two
    # Mikans (and hence `.mki` interface formats) agree.
    cubical.url = "github:stschaef/cubical/mikan-pinned";
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
    mikan,
    cubical,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        lib = pkgs.lib;

        mikanBare = mikan.packages.${system}.default;

        # ---- Deployed / store cubical (default) -------------------------------
        # Mikan already wrapped with the pinned, Mikan-built cubical on its
        # `--library-file`, provided by the cubical flake. Hermetic; builds the
        # store cubical once.
        mikanWithStoreCubical = cubical.packages.${system}.mikanWithCubical;

        # ---- Local / on-disk cubical (override) -------------------------------
        # Default directory of the sibling cubical checkout; override per-shell
        # with the CUBICAL_LIBDIR environment variable (e.g. in .envrc). This
        # wrapper points Mikan at that directory's `cubical.agda-lib` and its
        # locally-built `_build/<ver>/mikan/*.mki` — no Nix build of cubical at
        # all, so edits there never trigger a rebuild here (and vice versa).
        cubicalLocalDefault = "/Users/stevenschaefer/cubical";

        mikanWithLocalCubical = pkgs.writeShellScriptBin "mikan" ''
          set -eu
          libdir="''${CUBICAL_LIBDIR:-${cubicalLocalDefault}}"
          if [ ! -f "$libdir/cubical.agda-lib" ]; then
            echo "mikan(local): no cubical.agda-lib under '$libdir'." >&2
            echo "  Set CUBICAL_LIBDIR to your cubical checkout." >&2
            exit 1
          fi
          libfile="$(mktemp)"
          printf '%s\n' "$libdir/cubical.agda-lib" > "$libfile"
          exec ${lib.getExe mikanBare} --library-file="$libfile" "$@"
        '';

        mkShell = mikanPkg: pkgs.mkShell {
          AGDA_BIN = "mikan";
          nativeBuildInputs = [
            mikanPkg
            pkgs.haskellPackages.fix-whitespace
          ];
        };
      in
      {
        packages = {
          mikan = mikanBare;
          cubical = cubical.packages.${system}.cubical;
          default = mikanBare;
        };

        devShells = {
          # `nix develop` (and `.envrc` -> `use flake`): the deployed, pinned,
          # Mikan-built cubical from the Nix store. Builds cubical once; stable
          # while you work here.
          default = mkShell mikanWithStoreCubical;

          # `nix develop .#local` (or `.envrc` -> `use flake .#local`): point
          # Mikan at the on-disk cubical checkout (CUBICAL_LIBDIR, default
          # ${cubicalLocalDefault}). No Nix build of cubical — use this when
          # co-developing cubical and this library together.
          local = mkShell mikanWithLocalCubical;
        };
      }
    );
}
