{pkgs ? import <nixpkgs> {}}:
pkgs.mkShell {
  buildInputs = with pkgs;
    [
      gnumake
    ]
    ++ [
      (haskellPackages.ghcWithPackages (ghcPkgs:
        with ghcPkgs; [
          haskell-language-server
          mtl
          haskeline
          directory
          BNFC
          alex
          happy
          QuickCheck
        ]))
    ];
}
