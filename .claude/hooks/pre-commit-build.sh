#!/usr/bin/env bash
# Pre-commit hook: runs full `lake build` before any `jj commit`.
# If the build fails, the commit is blocked.
# Also checks that all .lean files are in the build graph (imported by Instances.lean etc.)

INPUT=$(cat)
COMMAND=$(echo "$INPUT" | jq -r '.tool_input.command')

# Check if the command contains "jj commit"
if echo "$COMMAND" | grep -q "jj commit"; then
  cd /home/heartpunk/code/learnability

  # Step 1: Check all .lean files are in the build graph
  echo "Pre-commit hook: checking all .lean files are imported..." >&2
  ORPHANS=""
  for f in $(find Instances Core SymExec Learnability -name '*.lean' -not -path '*/.lake/*' 2>/dev/null | sort); do
    # Convert path to module name: Instances/ISAs/Foo.lean -> Instances.ISAs.Foo
    MOD=$(echo "$f" | sed 's|/|.|g; s|\.lean$||')
    # Check if this module is imported anywhere in any .lean file
    if ! grep -rq "import ${MOD}$" --include='*.lean' . 2>/dev/null; then
      ORPHANS="$ORPHANS  $MOD\n"
    fi
  done
  if [ -n "$ORPHANS" ]; then
    echo "ORPHAN FILES not in build graph:" >&2
    echo -e "$ORPHANS" >&2
    echo '{"decision":"block","reason":"Orphan .lean files not imported by any module. Add them to Instances.lean or the appropriate root."}'
    exit 2
  fi

  # Step 2: Full lake build
  echo "Pre-commit hook: running full lake build..." >&2
  BUILD_OUTPUT=$(nix develop --command lake build 2>&1)
  BUILD_EXIT=$?

  if [ $BUILD_EXIT -ne 0 ]; then
    echo "BUILD FAILED — commit blocked." >&2
    echo "$BUILD_OUTPUT" | tail -20 >&2
    echo '{"decision":"block","reason":"Full lake build failed. Fix build errors before committing."}'
    exit 2
  else
    echo "Build passed." >&2
  fi
fi

exit 0
