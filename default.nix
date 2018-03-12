{ mkDerivation, base, contravariant, product-profunctors
, profunctors, reflex, reflex-dom, stdenv
}:
mkDerivation {
  pname = "reflex-elm";
  version = "0.1.0";
  src = ./.;
  libraryHaskellDepends = [
    base contravariant product-profunctors profunctors reflex
    reflex-dom
  ];
  description = "Synopsis";
  license = stdenv.lib.licenses.gpl3;
}
