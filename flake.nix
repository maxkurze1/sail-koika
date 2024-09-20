{
  inputs = {
    nixpkgs.follows = "koika/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    koika.url = "git+file:///home/samxamnam/Projects/koika?ref=master";
    coq-sail.url = "github:maxkurze1/coq-sail";
    coq-bbv.url = "github:maxkurze1/bbv";
  };
  outputs = { self, nixpkgs, flake-utils, koika, coq-sail, coq-bbv, ... }:
    let
      SailKoikaPkg = { lib, mkCoqDerivation, coq, koika, coq-sail, coq-bbv }: mkCoqDerivation rec {
        pname = "sail-koika";
        defaultVersion = "0.0.1";

        opam-name = "sail-koika";
        useDune = true;

        release."0.0.1" = {
          src = lib.const (lib.cleanSourceWith {
            src = lib.cleanSource ./.;
            filter = let inherit (lib) hasSuffix; in
              path: type:
                (! hasSuffix ".gitignore" path)
                && (! hasSuffix "flake.nix" path)
                && (! hasSuffix "flake.lock" path)
                && (! hasSuffix "_build" path);
          });
        };

        propagatedBuildInputs = [ coq koika coq-sail coq-bbv ];
      };
    in
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [
              # new 0.17.1 sail version
              (_: prev: {
                ocamlPackages = prev.ocamlPackages.overrideScope (_: ocaml_prev: {
                  sail = ocaml_prev.sail.overrideAttrs
                    (old: rec {
                      version = "0.17.1";
                      src = prev.fetchFromGitHub {
                        owner = "rems-project";
                        repo = "sail";
                        rev = version;
                        hash = "sha256-wnjiIadTE5FoTrX7hl2Ulk8vA80AdJRvtmaN+2kQFWY=";
                      };
                      propagatedBuildInputs = old.propagatedBuildInputs ++ [ ocaml_prev.menhirLib ];
                    });
                });
              })
              coq-bbv.overlays.default
              coq-sail.overlays.default
              koika.overlays.default
              self.overlays.default
            ];
          };
        in
        rec {
          devShells.default = packages.default.overrideAttrs (_: {
            buildInputs = with pkgs; [ ocamlPackages.sail z3 ];
            shellHook = ''
              [[ -v SHELL ]] && exec "$SHELL"
            '';
          });

          packages = rec {
            coq8_18-sail-koika = pkgs.coqPackages_8_18.sail-koika;
            default = coq8_18-sail-koika;
          };
        }) // {
      overlays.default = final: prev:
        (nixpkgs.lib.mapAttrs
          (_: scope:
            scope.overrideScope (self: _: {
              sail-koika = self.callPackage SailKoikaPkg { };
            })
          )
          {
            inherit (prev) coqPackages_8_18;
          }
        );
    };
}
