{pkgs ? import <nixpkgs> {}}:
pkgs.stdenv.mkDerivation {
  pname = "cubicaltt";
  version = "1.0";

  src = ./.;
  buildInputs = (import ./deps.nix {inherit pkgs;}).buildInputs;
  installPhase = ''
    mkdir -p $out/bin
    mv ./cubical $out/bin
  '';
}
