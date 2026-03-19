{
  description = "learnability VEX reference environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    lean4-nix.url = "github:lenianiva/lean4-nix";
    angr-nix.url = "github:heartpunk/angr-nix/2f20f9ed68506bd151ed171e505942ac9a2a0b43";
    stalagmite = {
      url = "github:leonbett/stalagmite/eadeecfd0845859e78d7390270a7bee31f57bc71";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, lean4-nix, angr-nix, stalagmite }:
    let
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-linux"
      ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f system);
    in {
      # Terminal emulator .o files for VEX extraction (x86_64-linux only)
      packages = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
        in pkgs.lib.optionalAttrs pkgs.stdenv.isLinux {

          # libtsm: terminal state machine — tsm-vte.c + tsm-vte-charsets.c
          libtsm-obj = pkgs.stdenv.mkDerivation {
            pname = "libtsm-obj";
            version = pkgs.libtsm.version;
            src = pkgs.libtsm.src;
            nativeBuildInputs = [ pkgs.pkg-config ];
            buildInputs = [ pkgs.libxkbcommon ];
            dontConfigure = true;
            dontInstall = false;
            buildPhase = ''
              CFLAGS="-O0 -g -U_FORTIFY_SOURCE $(pkg-config --cflags xkbcommon) -I src/tsm -I src/shared -I external/wcwidth"
              gcc -c $CFLAGS -o tsm-vte.o src/tsm/tsm-vte.c
              gcc -c $CFLAGS -o tsm-vte-charsets.o src/tsm/tsm-vte-charsets.c
              gcc -c $CFLAGS -o tsm-unicode.o src/tsm/tsm-unicode.c
              gcc -c $CFLAGS -o tsm-screen.o src/tsm/tsm-screen.c
              gcc -c $CFLAGS -o tsm-render.o src/tsm/tsm-render.c
              gcc -c $CFLAGS -o tsm-selection.o src/tsm/tsm-selection.c
              gcc -c $CFLAGS -o shl-htable.o src/shared/shl-htable.c
              ld -r -o libtsm.o tsm-vte.o tsm-vte-charsets.o tsm-unicode.o tsm-screen.o tsm-render.o tsm-selection.o shl-htable.o
            '';
            installPhase = ''
              mkdir -p $out
              cp libtsm.o $out/
              # Also keep individual .o files for targeted extraction
              cp tsm-vte.o $out/
              cp tsm-vte-charsets.o $out/
            '';
          };

          # st: suckless terminal — st.c only (no X11 window code)
          st-obj = pkgs.stdenv.mkDerivation {
            pname = "st-obj";
            version = pkgs.st.version;
            src = pkgs.st.src;
            nativeBuildInputs = [ pkgs.pkg-config pkgs.ncurses pkgs.fontconfig pkgs.freetype ];
            buildInputs = [ pkgs.libX11 pkgs.libXft ];
            dontConfigure = true;
            buildPhase = ''
              # st.c needs config.h — generate from default
              cp config.def.h config.h
              CFLAGS="-O0 -g -U_FORTIFY_SOURCE -D_XOPEN_SOURCE=600 $(pkg-config --cflags x11 xft fontconfig freetype2)"
              gcc -c $CFLAGS -o st.o st.c
            '';
            installPhase = ''
              mkdir -p $out
              cp st.o $out/
            '';
          };

          # libvte: GNOME terminal emulator library — parser core
          # Build the full meson project at -O0, then extract parser.cc.o
          libvte-obj = pkgs.stdenv.mkDerivation {
            pname = "libvte-obj";
            version = pkgs.vte.version;
            src = pkgs.vte.src;
            patches = pkgs.vte.patches or [];
            nativeBuildInputs = with pkgs; [
              desktop-file-utils gettext gobject-introspection gperf
              libxml2 meson ninja pkg-config vala python3 gi-docgen
            ];
            buildInputs = with pkgs; [
              cairo fribidi gnutls pango pcre2 lz4 icu fast-float
              simdutf systemd gtk3 glib fmt_11
            ];
            # Override meson optimization to -O0 for clean VEX IR
            mesonFlags = [
              "-Ddocs=false"
              "-Dapp=false"
              "-Dgtk3=true"
              "-Dgtk4=false"
              "--buildtype=debug"
              "--optimization=0"
            ];
            postPatch = ''
              patchShebangs perf/* \
                src/app/meson_desktopfile.py \
                src/parser-seq.py \
                src/minifont-coverage.py \
                src/modes.py
            '';
            # Build only enough to get the parser .o
            dontConfigure = true;
            buildPhase = ''
              meson setup builddir . --prefix=$out \
                -Ddocs=false -Dapp=false -Dgtk3=true -Dgtk4=false \
                --buildtype=debug --optimization=0
              # Build the full library (meson doesn't support partial .o targets easily)
              ninja -C builddir || true
            '';
            installPhase = ''
              mkdir -p $out
              # Find the parser .o file in the build tree
              find builddir -name 'parser*.o' -exec cp {} $out/ \;
              # Also grab vteseq if available
              find builddir -name 'vteseq*.o' -exec cp {} $out/ \; 2>/dev/null || true
              ls -la $out/
            '';
          };

          # QuickJS: JavaScript engine — single-file bytecode interpreter
          quickjs-obj = pkgs.stdenv.mkDerivation {
            pname = "quickjs-obj";
            version = pkgs.quickjs.version;
            src = pkgs.quickjs.src;
            dontConfigure = true;
            buildPhase = ''
              CFLAGS="-O0 -g -U_FORTIFY_SOURCE -D_GNU_SOURCE -DCONFIG_VERSION=\"${pkgs.quickjs.version}\" -DCONFIG_BIGNUM"
              gcc -c $CFLAGS -o quickjs.o quickjs.c
            '';
            installPhase = ''
              mkdir -p $out
              cp quickjs.o $out/
            '';
          };

          # Lua 5.4: bytecode interpreter — lvm.c is the core eval loop
          lua-obj = pkgs.stdenv.mkDerivation {
            pname = "lua-obj";
            version = pkgs.lua5_4.version;
            src = pkgs.lua5_4.src;
            dontConfigure = true;
            buildPhase = ''
              CFLAGS="-O0 -g -U_FORTIFY_SOURCE -DLUA_USE_LINUX -I src"
              for f in src/lvm.c src/ldo.c src/lapi.c src/lgc.c src/lstate.c src/ltable.c src/lobject.c src/lstring.c src/lfunc.c src/lmem.c src/ldebug.c src/llex.c src/lparser.c src/lcode.c src/lopcodes.c src/ltm.c src/lundump.c src/ldump.c src/lzio.c src/lctype.c src/lbaselib.c src/lauxlib.c; do
                gcc -c $CFLAGS -o $(basename ''${f%.c}.o) $f
              done
              ld -r -o lua.o lvm.o ldo.o lapi.o lgc.o lstate.o ltable.o lobject.o lstring.o lfunc.o lmem.o ldebug.o llex.o lparser.o lcode.o lopcodes.o ltm.o lundump.o ldump.o lzio.o lctype.o lbaselib.o lauxlib.o
            '';
            installPhase = ''
              mkdir -p $out
              cp lua.o $out/
              cp lvm.o $out/
              cp llex.o $out/
              cp lparser.o $out/
            '';
          };

        });

      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
          };
        in {
          default = pkgs.mkShell {
            packages = [
              pkgs.lean
              angr-nix.packages.${system}.default
              pkgs.git
              pkgs.jujutsu
              pkgs.uv
              pkgs.jq
              pkgs.cvc5
              pkgs.just
            ] ++ pkgs.lib.optionals pkgs.stdenv.isLinux [
              pkgs.gcc
              pkgs.binutils
              pkgs.boehmgc
            ];
            env = {
              UV_NO_MANAGED_PYTHON = "1";
              UV_PYTHON_DOWNLOADS = "never";
            };
          };
        });
    };
}
