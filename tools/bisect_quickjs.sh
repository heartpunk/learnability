#!/usr/bin/env bash
# Bisect test: does QuickJS JS_CallInternal get past block parsing within 60s?
# Exit 0 = good (parses fast), Exit 1 = bad (hangs), Exit 125 = skip (build fails)
set -euo pipefail

# Build
lake build dispatchLoopEval 2>/dev/null || exit 125

# Run with 60s timeout, check if it gets past "body branches" line
timeout 60 .lake/build/bin/dispatchLoopEval \
  reference/quickjs/blocks_core.json \
  --functions JS_CallInternal \
  --log /tmp/bisect_quickjs.log 2>&1 > /dev/null || true

# Check if it got past parsing (should see "body branches" in log)
if grep -q "body branches" /tmp/bisect_quickjs.log 2>/dev/null; then
  echo "GOOD: parsed successfully"
  exit 0
else
  echo "BAD: did not parse within 60s"
  exit 1
fi
