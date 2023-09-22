{
  pkgs ? import <nixpkgs> {},
  devDeps ? (ghcPkgs: []),
}: {
  buildInputs = with pkgs;
    [
      gnumake
    ]
    ++ [
      (
        haskellPackages.ghcWithPackages (ghcPkgs:
          (with ghcPkgs; [
            mtl
            haskeline
            directory
            BNFC
            alex
            happy
            QuickCheck
          ])
          ++ devDeps ghcPkgs)
      )
    ];
}
