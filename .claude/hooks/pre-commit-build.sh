#!/bin/bash
# Pre-commit hook: runs full `lake build` before any `jj commit`.
# If the build fails, the commit is blocked.

INPUT=$(cat)
COMMAND=$(echo "$INPUT" | jq -r '.tool_input.command')

# Check if the command contains "jj commit"
if echo "$COMMAND" | grep -q "jj commit"; then
  echo "Pre-commit hook: running full lake build..." >&2
  cd /home/heartpunk/code/learnability
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
