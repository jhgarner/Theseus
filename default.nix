let
  pkgs = import <nixpkgs> { };
  docco = pkgs.buildNpmPackage rec {
    pname = "docco";
    version = "0.9.2";

    src = pkgs.fetchFromGitHub {
      owner = "jashkenas";
      repo = "docco";
      rev = version;
      hash = "sha256-ze6T60oyVhzjFwg20QgO9WRcGH/9Yz1oNYTX2Tn9I7Y=";  # You'll need to fill this in
    };

    npmDepsHash = "sha256-OexhFqXZJFj39Bg/nMQomLFVREiW9Z61fQ0d0ypCOlo=";
    dontNpmBuild = true;
  };
  docs = pkgs.stdenv.mkDerivation {
    name = "docs";
    srcs = ./src;
    tests = ./test;
    docPage = ./docPage;

    buildInputs = with pkgs; [
      findutils
      gnused
      docco
    ];

    buildPhase = ''
      # Run docco to generate documentation
      shopt -s globstar
      mkdir src
      cp -r $srcs/* src
      mkdir test
      cp -r $tests/* test
      docco -t $docPage/page.jst -c $docPage/page.css src/**/*.hs test/**/*.hs
      
      # Some doc lines begin with | because of Haddocks. This removes that.
      find docs -type f -exec sed -i 's/<p>|/<p>/g' {} +
    '';

    installPhase = ''
      # Copy docs to the output root
      mkdir -p $out
      cp -r docs/* $out/
    '';
  };
in
  { inherit docs; }
