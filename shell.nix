{pkgs ? import <nixpkgs> {}}:
pkgs.mkShell {
  buildInputs =
    (import ./deps.nix {
      inherit pkgs;
      devDeps = ghcPkgs: with ghcPkgs; [haskell-language-server];
    })
    .buildInputs;
}
