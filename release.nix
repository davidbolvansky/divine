{ nixpkgs ? <nixpkgs>, divineSrc, release ? false, buildType ? "Debug" }:

let
  pkgs = import nixpkgs {};
  debuild = args:
    import ./nix/debian_build.nix ({ stdenv = pkgs.stdenv; vmTools = pkgs.vmTools; } // args);
  rpmbuild = pkgs.releaseTools.rpmBuild;
  rpmbuild_i386 = pkgs.pkgsi686Linux.releaseTools.rpmBuild;
  vmImgs = pkgs.vmTools.diskImageFuns;
  lib = pkgs.lib;

  wimlib = pkgs.callPackage nix/wimlib.nix {};
  windows7_iso = pkgs.fetchurl {
    url = "http://msft.digitalrivercontent.net/win/X17-59183.iso";
    sha256 = "13l3skfp3qi2ccv9djhpg7a7f2g57rph8n38dnkw8yh8w1bdyk7x";
  };

  windows7_img = pkgs.callPackage nix/windows_img.nix {
    inherit wimlib;
    iso = windows7_iso;
    name = "windows7";
  };
  windows_cmake = pkgs.callPackage nix/windows_cmake.nix {};
  windows_mingw = pkgs.callPackage nix/windows_mingw.nix {};
  windows_nsis = pkgs.callPackage nix/windows_nsis.nix {};
  windows_qt = pkgs.callPackage nix/windows_qt.nix {};

  extra_debs = [ "cmake" "build-essential" "debhelper" "m4"
                 "libqt4-dev" "libboost-dev" "libncurses5-dev" ];
  extra_rpms = [ "cmake" ];

  mkVM = { VM, extras, diskFun, mem ? 3072 }:
   VM rec {
     name = "divine";
     src = jobs.tarball;
     diskImage = diskFun { extraPackages = extras; };
     configurePhase = "echo -DCMAKE_BUILD_TYPE=${buildType} > pkgbuildflags";
     doCheck = false; # the package builder is supposed to run checks
     memSize = mem;
   };

  mkbuild = { name, inputs }: { system ? builtins.currentSystem }:
    let pkgs = import nixpkgs { inherit system; }; in
    pkgs.releaseTools.nixBuild {
       name = "divine-" + name;
       src = jobs.tarball;
       buildInputs = [ pkgs.gcc47 pkgs.cmake pkgs.perl pkgs.m4 ] ++ inputs { inherit pkgs; };
       cmakeFlags = [ "-DCMAKE_BUILD_TYPE=${buildType}" ];
       checkPhase = ''
          make unit || touch $out/nix-support/failed
          make functional || touch $out/nix-support/failed
       '';
    };

  mkwin = image: flags: pkgs.callPackage nix/windows_build.nix {
    inherit windows_mingw;
    tools = [ windows_cmake windows_nsis windows_qt ];
    img = image;
    src = jobs.tarball;
    name = "divine";
    mem = "2048M";
    buildScript = ''
      set -ex
      mkdir build && cd build
      # Windows/mingw breaks on big files :-(
      bt=${buildType}
      test "$bt" = "RelWithDebInfo" && echo ${flags} | grep -v SMALL && bt=Release
      cmake -G "MSYS Makefiles" -DRX_PATH=D:\\mingw\\include -BUILD_DCMAKE_TYPE=$bt ${flags} ../source
      make
      mkdir E:\\nix-support
      make unit || touch E:\\nix-support\\failed
      make functional || touch E:\\nix-support\\failed
      make package
      cp tools/divine.exe E:/
      cp divine-*.exe E:/
    '';
  };

  versionFile = builtins.readFile ./divine/utility/version.cpp;
  versionLine = builtins.head (
    lib.filter (str: lib.eqStrings (builtins.substring 0 22 str) "#define DIVINE_VERSION")
               (lib.splitString "\n" versionFile));
  version = builtins.head (builtins.tail (lib.splitString "\"" (versionLine + " ")));

  jobs = rec {

    tarball = pkgs.releaseTools.sourceTarball rec {
        inherit version;
        name = "divine-tarball";
        versionSuffix = if divineSrc ? revCount
                           then "+pre${toString divineSrc.revCount}"
                           else "";
        src = divineSrc;
        buildInputs = (with pkgs; [ cmake gcc47 ]);
        cmakeFlags = [ "-DVERSION_APPEND=${versionSuffix}" ];
        autoconfPhase = ''
          sed -e "s,^\(Version:.*\)0$,\1${version}${versionSuffix}," -i divine.spec
          sed -e 's,"","${versionSuffix}",' -i cmake/VersionAppend.cmake

          mv debian/changelog debian/changelog.xxx
          echo "divine (${version}${versionSuffix}) unstable; urgency=low" >> debian/changelog
          echo >> debian/changelog
          echo "  * Automated Hydra build" >> debian/changelog
          echo >> debian/changelog
          echo " -- Petr Rockai <mornfall@debian.org>  `date -R`" >> debian/changelog
          echo >> debian/changelog
          cat debian/changelog.xxx >> debian/changelog
          rm debian/changelog.xxx

          chmod +x configure # ha-ha
        '';
        distPhase = ''
            make package_source
            mkdir $out/tarballs
            cp divine-*.tar.gz $out/tarballs
        '';
      };

    manual =
     let tex = pkgs.texLiveAggregationFun { paths = [ pkgs.texLive pkgs.lmodern ]; };
          in pkgs.releaseTools.nixBuild {
              name = "divine-manual";
              src = jobs.tarball;
              buildInputs = [ pkgs.gcc47 pkgs.cmake pkgs.perl pkgs.haskellPackages.pandoc tex ];
              buildPhase = "make manual website";
              installPhase = ''
                mkdir $out/manual $out/website
                cp manual/manual.pdf manual/manual.html $out/manual/
                cp website/*.html website/*.png website/*.css $out/website/
                cp ../website/template.html $out/website
              '';
              checkPhase = ":";
          };

    minimal = mkbuild { name = "minimal"; inputs = { pkgs }: []; };
    mpi = mkbuild { name = "mpi"; inputs = { pkgs }: [ pkgs.openmpi ]; };
    gui = mkbuild { name = "gui"; inputs = { pkgs }: [ pkgs.qt4 ]; };
    llvm = mkbuild { name = "llvm"; inputs = { pkgs }: [ pkgs.llvm pkgs.clang ]; };
    timed = mkbuild { name = "timed"; inputs = { pkgs }: [ pkgs.libxml2 pkgs.boost ]; };
    full = mkbuild { name = "full"; inputs = { pkgs }:
                      [ pkgs.openmpi pkgs.llvm pkgs.clang pkgs.qt4 pkgs.libxml2 pkgs.boost ]; };

    ubuntu1210_i386 = mkVM { VM = debuild; diskFun = vmImgs.ubuntu1210i386; extras = extra_debs; };
    fedora17_i386 = mkVM { VM = rpmbuild_i386; diskFun = vmImgs.fedora17i386; extras = extra_rpms; };

    ubuntu1210_x86_64 = mkVM { VM = debuild; diskFun = vmImgs.ubuntu1210x86_64; extras = extra_debs; mem = 3072; };
    fedora17_x86_64 = mkVM { VM = rpmbuild; diskFun = vmImgs.fedora17x86_64; extras = extra_rpms; };

    win7_i386_small = mkwin windows7_img "-DSMALL=ON";
    win7_i386 = mkwin windows7_img "";
  };
in
  jobs
