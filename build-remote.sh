#!/usr/bin/env bash
# Build a Lean target on abraxas via rsync + ssh.
# Usage: ./build-remote.sh [LAKE_TARGET]
# Default target: Instances.ISAs.VexCompTree
#
# First run: fetches packages + downloads mathlib cache (slow, ~minutes).
# Subsequent runs: rsyncs changed sources and rebuilds (fast).

TARGET="${1:-Instances.ISAs.VexCompTree}"
REMOTE="abraxas"
REMOTE_DIR="/tmp/learnability-cslib"

set -euo pipefail

echo "=== Syncing source to $REMOTE:$REMOTE_DIR ==="
rsync -az \
  --exclude='.lake' --exclude='.jj' --exclude='.git' \
  --exclude='lake-manifest.json' \
  /Users/heartpunk/workspaces/learnability-cslib/ \
  "$REMOTE:$REMOTE_DIR/"

ssh "$REMOTE" env LAKE_TARGET="$TARGET" bash << 'ENDSSH'
set -euo pipefail
cd /tmp/learnability-cslib

# Remove mac-specific packagesDir; use lake default (.lake/packages/)
sed -i '/packagesDir = /d' lakefile.toml

# ProofWidgets post-update hook needs this to exist before lake update
mkdir -p .lake/packages/proofwidgets/.lake/build/lib

# If no manifest yet (first run), fetch everything
if [ ! -f lake-manifest.json ]; then
  echo "--- First-time setup: fetching packages ---"
  nix develop --command lake update
  echo "--- Fetching mathlib prebuilt cache ---"
  nix develop --command lake exe cache get
fi

echo "--- Building $LAKE_TARGET ---"
nix develop --command lake build "$LAKE_TARGET" 2>&1
ENDSSH
