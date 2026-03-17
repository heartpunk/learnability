<<<<<<< conflict 1 of 1
+++++++ yxkvzmyx f455a21b (rebase destination)
%%%%%%% diff from: oqqtmuzq 1c97f471 "Add justfile + stalagmite flake input + per-function VEX extraction" (parents of rebased revision)
\\\\\\\        to: xkystpsr 5c013e36 "Add --entry and --functions scoping, classifier-based grammar filtering" (rebased revision)
 # Learnability pipeline task runner
 # Requires: nix develop (for deps), lake build (for Lean executables)
 
 set shell := ["bash", "-euo", "pipefail", "-c"]
 
 # Stalagmite source (set by nix devShell, or override manually)
 stalagmite_src := env("STALAGMITE_SRC", "")
 stalagmite_rev := "eadeecfd0845859e78d7390270a7bee31f57bc71"
 
 # All test subjects
 subjects := "tinyc json cjson parson lisp calc simplearithmeticparser cgi_decode mjs"
 
 # Remote builder for cross-arch extraction (assumes ambient ssh + nix)
 remote := "abraxas"
 remote_stalagmite := "~/code/stalagmite"
 remote_flake := "~/code/learnability"
 
 # ── Subject source map ────────────────────────────────────────────
 # Each entry: subject_name:source1.c,source2.c[:cpp]
 # Suffix :cpp means use g++ instead of gcc
 
+# Sources per subject
 _src_tinyc := "tiny_orig.c"
 _src_json := "json_orig.c,vector.c"
 _src_cjson := "cJSON_orig.c,cJSON_Utils.c"
 _src_parson := "parson_orig.c"
 _src_lisp := "parse_orig.c,runtime.c"
 _src_calc := "calc.c,opp.c,rdp_orig.c"
 _src_simplearithmeticparser := "parser_orig.cpp"
 _src_cgi_decode := "cgi_decode_orig.c"
 _src_mjs := "mjs_orig.c"
 
+# Parser functions per subject (comma-separated, for --functions scoping)
+_funcs_tinyc := "next_sym,term,sum,test,expr,paren_expr,statement"
+_funcs_json := ""
+_funcs_cjson := ""
+_funcs_parson := ""
+_funcs_lisp := ""
+_funcs_calc := ""
+_funcs_simplearithmeticparser := ""
+_funcs_cgi_decode := ""
+_funcs_mjs := ""
+
 # ── Extraction ────────────────────────────────────────────────────
 
 # Extract VEX blocks for a subject: compile .o, run pyvex linear sweep
 extract subject:
     #!/usr/bin/env bash
     set -euo pipefail
 
     SUBJECT="{{subject}}"
     # Look up sources from the map
     case "$SUBJECT" in
         tinyc)                   SOURCES="{{_src_tinyc}}" ;;
         json)                    SOURCES="{{_src_json}}" ;;
         cjson)                   SOURCES="{{_src_cjson}}" ;;
         parson)                  SOURCES="{{_src_parson}}" ;;
         lisp)                    SOURCES="{{_src_lisp}}" ;;
         calc)                    SOURCES="{{_src_calc}}" ;;
         simplearithmeticparser)  SOURCES="{{_src_simplearithmeticparser}}" ;;
         cgi_decode)              SOURCES="{{_src_cgi_decode}}" ;;
         mjs)                     SOURCES="{{_src_mjs}}" ;;
         *) echo "Unknown subject: $SUBJECT"; exit 1 ;;
     esac
     IFS=',' read -ra SRC_ARRAY <<< "$SOURCES"
     OUT_DIR="reference/$SUBJECT"
     mkdir -p "$OUT_DIR"
 
     if [[ "$(uname -m)" == "x86_64" ]] && [[ "$(uname -s)" == "Linux" ]]; then
         SRC_DIR="${STALAGMITE_SRC}/subjects/$SUBJECT"
         WORK=$(mktemp -d)
         trap "rm -rf $WORK" EXIT
 
         # Compile each source
         for src in "${SRC_ARRAY[@]}"; do
             obj="${src%.*}.o"
             ext="${src##*.}"
             if [[ "$ext" == "cpp" ]]; then
                 g++ -c -O0 -o "$WORK/$obj" "$SRC_DIR/$src"
             else
-                gcc -c -O0 -o "$WORK/$obj" "$SRC_DIR/$src"
+                gcc -c -O0 -Wno-incompatible-pointer-types -Wno-int-conversion -o "$WORK/$obj" "$SRC_DIR/$src"
             fi
         done
 
         # Merge if multiple objects, otherwise just copy
         OBJ_COUNT=$(ls "$WORK"/*.o | wc -l)
         if [[ "$OBJ_COUNT" -eq 1 ]]; then
             cp "$WORK"/*.o "$OUT_DIR/$SUBJECT.o"
         else
             ld -r -o "$OUT_DIR/$SUBJECT.o" "$WORK"/*.o
         fi
 
         # Extract VEX blocks
         python3 tools/vex_ref/extract_cfg.py "$OUT_DIR/$SUBJECT.o" --per-function \
             > "$OUT_DIR/blocks.json"
     else
         # Remote build on {{remote}}
         REMOTE_WORK=$(ssh {{remote}} "mktemp -d")
         trap "ssh {{remote}} 'rm -rf $REMOTE_WORK'" EXIT
 
         REMOTE_SRC="{{remote_stalagmite}}/subjects/$SUBJECT"
 
         # Copy sources to temp dir (avoids modifying stalagmite checkout)
         ssh {{remote}} "for src in ${SRC_ARRAY[*]}; do cp $REMOTE_SRC/\$src $REMOTE_WORK/; done"
 
         # Copy extraction script
         scp -q tools/vex_ref/extract_cfg.py "{{remote}}:$REMOTE_WORK/"
 
         # Compile + merge + extract (all need nix devShell for gcc/python3/angr)
         ssh {{remote}} "nix develop {{remote_flake}} --command bash -c '
             cd $REMOTE_WORK
             for src in ${SRC_ARRAY[*]}; do
                 ext=\${src##*.}; obj=\${src%.*}.o
                 if [ \"\$ext\" = cpp ]; then
                     g++ -c -O0 -o \$obj \$src
                 else
-                    gcc -c -O0 -o \$obj \$src
+                    gcc -c -O0 -Wno-incompatible-pointer-types -Wno-int-conversion -o \$obj \$src
                 fi
             done
             OBJ_COUNT=\$(ls *.o | wc -l)
             if [ \$OBJ_COUNT -eq 1 ]; then
                 cp *.o $SUBJECT.o
             else
                 ld -r -o $SUBJECT.o *.o
             fi
             python3 $REMOTE_WORK/extract_cfg.py $SUBJECT.o --per-function > blocks.json
         '"
 
         # Copy results back
         scp -q "{{remote}}:$REMOTE_WORK/$SUBJECT.o" "$OUT_DIR/"
         scp -q "{{remote}}:$REMOTE_WORK/blocks.json" "$OUT_DIR/"
     fi
 
     # Write provenance
     printf "subject: %s\nstalagmite_rev: %s\nsources: %s\nbuilt: %s\n" \
         "$SUBJECT" "{{stalagmite_rev}}" "$SOURCES" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
         > "$OUT_DIR/BUILD_INFO"
 
     echo "✓ $SUBJECT → $OUT_DIR/ ($(wc -c < "$OUT_DIR/$SUBJECT.o") bytes, $(python3 -c "import json; print(len(json.load(open('$OUT_DIR/blocks.json'))['blocks']))" 2>/dev/null || echo '?') blocks)"
 
 # Extract all subjects
 extract-all:
     for s in {{subjects}}; do just extract $s; done
 
 # ── Analysis ──────────────────────────────────────────────────────
 
 # Build the Lean pipeline (if needed)
 build:
     lake build dispatchLoopEval
 
-# Analyze a subject (text output) — per-function JSON has everything needed
+# Analyze a subject — uses --functions scoping if configured
 analyze subject *flags: build
-    lake exe dispatchLoopEval reference/{{subject}}/blocks.json {{flags}}
+    #!/usr/bin/env bash
+    set -euo pipefail
+    FUNCS=""
+    case "{{subject}}" in
+        tinyc)                   FUNCS="{{_funcs_tinyc}}" ;;
+        json)                    FUNCS="{{_funcs_json}}" ;;
+        cjson)                   FUNCS="{{_funcs_cjson}}" ;;
+        parson)                  FUNCS="{{_funcs_parson}}" ;;
+        lisp)                    FUNCS="{{_funcs_lisp}}" ;;
+        calc)                    FUNCS="{{_funcs_calc}}" ;;
+        simplearithmeticparser)  FUNCS="{{_funcs_simplearithmeticparser}}" ;;
+        cgi_decode)              FUNCS="{{_funcs_cgi_decode}}" ;;
+        mjs)                     FUNCS="{{_funcs_mjs}}" ;;
+    esac
+    FUNCS_FLAG=""
+    if [[ -n "$FUNCS" ]]; then
+        FUNCS_FLAG="--functions $FUNCS"
+    fi
+    lake exe dispatchLoopEval reference/{{subject}}/blocks.json $FUNCS_FLAG {{flags}}
 
 # Analyze a subject with JSON output
 analyze-json subject: build
-    lake exe dispatchLoopEval reference/{{subject}}/blocks.json --json
+    #!/usr/bin/env bash
+    set -euo pipefail
+    FUNCS=""
+    case "{{subject}}" in
+        tinyc)                   FUNCS="{{_funcs_tinyc}}" ;;
+        json)                    FUNCS="{{_funcs_json}}" ;;
+        cjson)                   FUNCS="{{_funcs_cjson}}" ;;
+        parson)                  FUNCS="{{_funcs_parson}}" ;;
+        lisp)                    FUNCS="{{_funcs_lisp}}" ;;
+        calc)                    FUNCS="{{_funcs_calc}}" ;;
+        simplearithmeticparser)  FUNCS="{{_funcs_simplearithmeticparser}}" ;;
+        cgi_decode)              FUNCS="{{_funcs_cgi_decode}}" ;;
+        mjs)                     FUNCS="{{_funcs_mjs}}" ;;
+    esac
+    FUNCS_FLAG=""
+    if [[ -n "$FUNCS" ]]; then
+        FUNCS_FLAG="--functions $FUNCS"
+    fi
+    lake exe dispatchLoopEval reference/{{subject}}/blocks.json $FUNCS_FLAG --json
 
 # Analyze all subjects
 analyze-all *flags: build
     for s in {{subjects}}; do \
         echo "═══ $s ═══"; \
         just analyze $s {{flags}} || true; \
         echo; \
     done
 
 # ── Testing ───────────────────────────────────────────────────────
 
 # Run test suite
 test: build
     lake exe dispatchLoopEval --test
 
 # Run test for a specific subject
 test-subject name: build
     lake exe dispatchLoopEval --test --subject {{name}}
 
 # ── Utilities ─────────────────────────────────────────────────────
 
 # Show golden grammar for a subject
 golden subject:
     @cat "{{stalagmite_src}}/data/golden_grammars/golden_grammar_{{subject}}.json"
 
 # List all subjects
 list:
     @echo {{subjects}} | tr ' ' '\n'
 
 # Show extraction status for all subjects
 status:
     @for s in {{subjects}}; do \
         if [ -f "reference/$s/blocks.json" ]; then \
             blocks=$(python3 -c "import json; print(len(json.load(open('reference/$s/blocks.json'))['blocks']))" 2>/dev/null || echo '?'); \
             echo "✓ $s ($blocks blocks)"; \
         else \
             echo "  $s (not extracted)"; \
         fi; \
     done
>>>>>>> conflict 1 of 1 ends
