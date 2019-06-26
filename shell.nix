{ nixpkgs ? import <nixpkgs> {}

 }:
let nixpkgs_source =
fetchTarball "https://github.com/NixOS/nixpkgs-channels/archive/nixos-19.03.tar.gz";
  nixpkgs' = (import nixpkgs_source){};
in with nixpkgs'.pkgs;
let pkg = haskellPackages.callPackage
            ({ mkDerivation, alex, array, base, BNFC, directory, filepath
             , happy, haskeline, mtl, stdenv, transformers
             }:
             mkDerivation {
               pname = "cubical";
               version = "0.2.0";
               src = ./.;
               isLibrary = false;
               isExecutable = true;
               buildDepends = [
                 array base BNFC directory filepath haskeline mtl transformers
               ];
               buildTools = [ alex happy ];
               homepage = "https://github.com/simhu/cubical";
               description = "Implementation of Univalence in Cubical Sets";
               license = stdenv.lib.licenses.mit;
             }) {};
in
  pkg.env
