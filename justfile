# Learnability pipeline task runner
# Requires: nix develop (for deps), lake build (for Lean executables)

set shell := ["bash", "-euo", "pipefail", "-c"]

# Stalagmite source (set by nix devShell, or override manually)
stalagmite_src := env("STALAGMITE_SRC", "")
stalagmite_rev := "eadeecfd0845859e78d7390270a7bee31f57bc71"

# All test subjects
subjects := "tinyc json cjson parson lisp calc simplearithmeticparser cgi_decode mjs"

# New subjects: terminal emulators + bytecode interpreters
terminal_subjects := "libtsm st"
interpreter_subjects := "lua quickjs"
all_subjects := subjects + " " + terminal_subjects + " " + interpreter_subjects

# Max concurrent analysis jobs
parallel_jobs := "8"

# Remote builder for cross-arch extraction (assumes ambient ssh + nix)
remote := "abraxas"
remote_stalagmite := "~/code/stalagmite"
remote_flake := "~/code/learnability"

# ── Subject source map ────────────────────────────────────────────
# Each entry: subject_name:source1.c,source2.c[:cpp]
# Suffix :cpp means use g++ instead of gcc

# Sources per subject
_src_tinyc := "tiny_orig.c"
_src_json := "json_orig.c,vector.c"
_src_cjson := "cJSON_orig.c,cJSON_Utils.c"
_src_parson := "parson_orig.c"
_src_lisp := "parse_orig.c,runtime.c"
_src_calc := "calc.c,opp.c,rdp_orig.c"
_src_simplearithmeticparser := "parser_orig.cpp"
_src_cgi_decode := "cgi_decode_orig.c"
_src_mjs := "mjs_orig.c"

# Parser functions per subject (comma-separated, for --functions scoping)
_funcs_tinyc := "next_sym,term,sum,test,expr,paren_expr,statement"
_funcs_json := "json_parse,json_parse_value,json_parse_array,json_parse_object,skip_whitespace,has_char,json_is_literal"
_funcs_cjson := "parse_value,parse_array,parse_object,parse_string,parse_number,parse_hex4,buffer_skip_whitespace,skip_utf8_bom,utf16_literal_to_utf8,cJSON_ParseWithLengthOpts"
_funcs_parson := "parse_value,parse_array_value,parse_object_value,parse_string_value,parse_number_value,parse_boolean_value,parse_null_value,process_string,parse_utf16,parse_utf16_hex,skip_quotes,json_validate"
_funcs_lisp := "lex,parse,parse_sexp,eat_tok,peek_tok"
_funcs_calc := "parse_expr,parse_expression,parse_mult,parse_op,parse_primary,parse_sum,opp_parse_expression,rdp_parse_expression"
_funcs_simplearithmeticparser := "_ZN6Parser16parse_expressionEv,_ZN6Parser10parse_termEv,_ZN6Parser12parse_factorEv,_ZN6Parser13parse_integerEv,_ZN6Parser15skip_whitespaceEv,_ZN6Parser5parseEv"
_funcs_cgi_decode := "cgi_decode"
_funcs_mjs := "parse_statement,parse_expression,parse_assignment,parse_ternary,parse_logical_or,parse_logical_and,parse_bitwise_or,parse_bitwise_xor,parse_bitwise_and,parse_equality,parse_comparison,parse_shifts,parse_plus_minus,parse_mul_div_rem,parse_unary,parse_postfix,parse_call_dot_mem,parse_literal,parse_block,parse_block_or_stmt,parse_if,parse_while,parse_for,parse_for_in,parse_return,parse_let,parse_function,parse_object_literal,parse_array_literal,parse_statement_list,parse_mjs,parse_expr,pnext,exec_expr,mjs_execute"

# New subject function scoping
_funcs_libtsm := "parse_data,do_action,do_csi,do_esc,do_execute,do_trans,csi_attribute,csi_mode,csi_dev_attr,csi_dsr,csi_compat_mode,do_dcs,do_osc"
_funcs_st := "csihandle,tputc,eschandle,tcontrolcode,tstrsequence,strhandle,tsetattr,tsetmode"
_funcs_lua := "luaV_execute"
_funcs_quickjs := "JS_CallInternal"

# Input files for new subjects
_input_libtsm := "reference/libtsm/blocks.json"
_input_st := "reference/st/blocks.json"
_input_lua := "reference/lua/blocks_lvm.json"
_input_quickjs := "reference/quickjs/blocks_core.json"

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
                gcc -c -O0 -Wno-incompatible-pointer-types -Wno-int-conversion -o "$WORK/$obj" "$SRC_DIR/$src"
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
                    gcc -c -O0 -Wno-incompatible-pointer-types -Wno-int-conversion -o \$obj \$src
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

# Analyze a subject — uses --functions scoping if configured
analyze subject *flags: build
    #!/usr/bin/env bash
    set -euo pipefail
    FUNCS=""
    FUNCS=""
    INPUT="reference/{{subject}}/blocks.json"
    case "{{subject}}" in
        tinyc)                   FUNCS="{{_funcs_tinyc}}" ;;
        json)                    FUNCS="{{_funcs_json}}" ;;
        cjson)                   FUNCS="{{_funcs_cjson}}" ;;
        parson)                  FUNCS="{{_funcs_parson}}" ;;
        lisp)                    FUNCS="{{_funcs_lisp}}" ;;
        calc)                    FUNCS="{{_funcs_calc}}" ;;
        simplearithmeticparser)  FUNCS="{{_funcs_simplearithmeticparser}}" ;;
        cgi_decode)              FUNCS="{{_funcs_cgi_decode}}" ;;
        mjs)                     FUNCS="{{_funcs_mjs}}" ;;
        libtsm)                  FUNCS="{{_funcs_libtsm}}"; INPUT="{{_input_libtsm}}" ;;
        st)                      FUNCS="{{_funcs_st}}"; INPUT="{{_input_st}}" ;;
        lua)                     FUNCS="{{_funcs_lua}}"; INPUT="{{_input_lua}}" ;;
        quickjs)                 FUNCS="{{_funcs_quickjs}}"; INPUT="{{_input_quickjs}}" ;;
    esac
    FUNCS_FLAG=""
    if [[ -n "$FUNCS" ]]; then
        FUNCS_FLAG="--functions $FUNCS"
    fi
    lake exe dispatchLoopEval "$INPUT" $FUNCS_FLAG {{flags}}

# Analyze a subject with JSON output
analyze-json subject: build
    #!/usr/bin/env bash
    set -euo pipefail
    FUNCS=""
    INPUT="reference/{{subject}}/blocks.json"
    case "{{subject}}" in
        tinyc)                   FUNCS="{{_funcs_tinyc}}" ;;
        json)                    FUNCS="{{_funcs_json}}" ;;
        cjson)                   FUNCS="{{_funcs_cjson}}" ;;
        parson)                  FUNCS="{{_funcs_parson}}" ;;
        lisp)                    FUNCS="{{_funcs_lisp}}" ;;
        calc)                    FUNCS="{{_funcs_calc}}" ;;
        simplearithmeticparser)  FUNCS="{{_funcs_simplearithmeticparser}}" ;;
        cgi_decode)              FUNCS="{{_funcs_cgi_decode}}" ;;
        mjs)                     FUNCS="{{_funcs_mjs}}" ;;
        libtsm)                  FUNCS="{{_funcs_libtsm}}"; INPUT="{{_input_libtsm}}" ;;
        st)                      FUNCS="{{_funcs_st}}"; INPUT="{{_input_st}}" ;;
        lua)                     FUNCS="{{_funcs_lua}}"; INPUT="{{_input_lua}}" ;;
        quickjs)                 FUNCS="{{_funcs_quickjs}}"; INPUT="{{_input_quickjs}}" ;;
    esac
    FUNCS_FLAG=""
    if [[ -n "$FUNCS" ]]; then
        FUNCS_FLAG="--functions $FUNCS"
    fi
    lake exe dispatchLoopEval "$INPUT" $FUNCS_FLAG --json

# Analyze all subjects (sequential)
analyze-all *flags: build
    #!/usr/bin/env bash
    set -euo pipefail
    RUNDIR=".lake/runs/$(date -Iseconds)"
    mkdir -p "$RUNDIR"
    echo "Results in $RUNDIR"
    for s in {{all_subjects}}; do
        echo "═══ $s ═══"
        just analyze $s {{flags}} 2>&1 | tee "$RUNDIR/${s}.log" || true
        echo
    done
    ln -sfn "$(basename $RUNDIR)" .lake/runs/latest

# Analyze all subjects in parallel (max jobs limited by memory)
# Builds once sequentially first, then runs analysis jobs in parallel via lake exe
analyze-all-parallel *flags: build
    #!/usr/bin/env bash
    set -euo pipefail
    JOBS={{parallel_jobs}}
    RUNDIR=".lake/runs/$(date -Iseconds)"
    mkdir -p "$RUNDIR"
    echo "Build complete. Running all subjects with $JOBS parallel jobs..."
    echo "Results in $RUNDIR"
    # Generate a runner script with justfile variables already interpolated
    HELPER=$(mktemp)
    cat > "$HELPER" <<EOF
    #!/usr/bin/env bash
    s="\$1"; shift
    RUNDIR="\$2"; shift
    FUNCS="" INPUT="reference/\$s/blocks.json"
    case "\$s" in
        tinyc)                   FUNCS="{{_funcs_tinyc}}" ;;
        json)                    FUNCS="{{_funcs_json}}" ;;
        cjson)                   FUNCS="{{_funcs_cjson}}" ;;
        parson)                  FUNCS="{{_funcs_parson}}" ;;
        lisp)                    FUNCS="{{_funcs_lisp}}" ;;
        calc)                    FUNCS="{{_funcs_calc}}" ;;
        simplearithmeticparser)  FUNCS="{{_funcs_simplearithmeticparser}}" ;;
        cgi_decode)              FUNCS="{{_funcs_cgi_decode}}" ;;
        mjs)                     FUNCS="{{_funcs_mjs}}" ;;
        libtsm)                  FUNCS="{{_funcs_libtsm}}"; INPUT="{{_input_libtsm}}" ;;
        st)                      FUNCS="{{_funcs_st}}"; INPUT="{{_input_st}}" ;;
        lua)                     FUNCS="{{_funcs_lua}}"; INPUT="{{_input_lua}}" ;;
        quickjs)                 FUNCS="{{_funcs_quickjs}}"; INPUT="{{_input_quickjs}}" ;;
    esac
    FUNCS_FLAG=""
    if [[ -n "\$FUNCS" ]]; then FUNCS_FLAG="--functions \$FUNCS"; fi
    stdbuf -oL -eL .lake/build/bin/dispatchLoopEval "\$INPUT" \$FUNCS_FLAG "\$@" > "\$RUNDIR/\${s}.log" 2>&1 \
        && echo "  \$s DONE" || echo "  \$s FAILED"
    EOF
    chmod +x "$HELPER"
    echo "{{all_subjects}}" | tr ' ' '\n' | xargs -P "$JOBS" -I {} bash "$HELPER" {} "$RUNDIR" {{flags}}
    rm -f "$HELPER"
    echo "=== Summary ($RUNDIR) ==="
    for s in {{all_subjects}}; do
        if [[ -f "$RUNDIR/${s}.log" ]]; then
            result=$(grep -aE "Fixpoint complete|PARSE ERROR|converged|Total:|Coverage:" "$RUNDIR/${s}.log" | tail -3)
            echo "  $s: $result"
        else
            echo "  $s: no log"
        fi
    done
    # Symlink latest run
    ln -sfn "$(basename $RUNDIR)" .lake/runs/latest

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
