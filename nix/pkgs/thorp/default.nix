{ thorpSrc, mvn2nix, stdenv, jdk11_headless, maven, makeWrapper, graphviz }:
let

  # This file was generated from mvn2nix pom.xml > mvn2nix-lock.json however one of the hashes was incorrect
  # and so was changed manually, see https://github.com/fzakaria/mvn2nix/issues/29
  # also the format in the json file is base32 but the error is reported in base64 so you need to convert
  # nix-hash --type sha256 --to-base16 $expectedHash
  mavenRepository = mvn2nix.buildMavenRepositoryFromLockFile { file = ./mvn2nix-lock.json; };
in
stdenv.mkDerivation rec {
  pname = "thorp";
  version = "2.0.1";
  name = "${pname}-${version}";
  src = thorpSrc;
  buildInputs = [ jdk11_headless maven makeWrapper graphviz ];
  buildPhase = ''
    echo "Building with maven repository ${mavenRepository}"
    mvn package --offline -Dmaven.repo.local=${mavenRepository}
  '';

  installPhase = ''
    # create the bin directory
    mkdir -p $out/bin

    # create a symbolic link for the lib directory
    ln -s ${mavenRepository} $out/lib

    # copy out the JAR
    # Maven already setup the classpath to use m2 repository layout
    # with the prefix of lib/
    cp app/target/${name}-jar-with-dependencies.jar $out/${name}.jar

    # create a wrapper that will automatically set the classpath
    # this should be the paths from the dependency derivation
    makeWrapper ${jdk11_headless}/bin/java $out/bin/${pname} \
          --add-flags "-jar $out/${name}.jar"
  '';
  meta = {
    description = "Synchronisation of files with S3 using the hash of the file contents.";
    homepage = "https://github.com/kemitix/thorp";
    license = stdenv.lib.licenses.mit;
  };
}
