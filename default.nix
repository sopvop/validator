{ mkDerivation, aeson, base, bifunctors, mtl, stdenv, text
, transformers, unordered-containers, vector
}:
mkDerivation {
  pname = "validator";
  version = "0.3.0.0";
  src = ./.;
  libraryHaskellDepends = [
    aeson base bifunctors mtl text transformers unordered-containers
    vector
  ];
  doCheck = false;
  description = "Library for validation user input";
  license = stdenv.lib.licenses.bsd3;
}
