#!/bin/bash

set -e

echo "Regenerating haskell-ci.yml with correct triggers..."

# Check if haskell-ci is available
if ! command -v haskell-ci &> /dev/null; then
    echo "Error: haskell-ci not found. Please install it first:"
    echo "  cabal install haskell-ci"
    exit 1
fi

# Regenerate the workflow
echo "Running haskell-ci regenerate..."
haskell-ci regenerate

# Fix the on: section to avoid duplicate runs
echo "Fixing triggers to avoid duplicate CI runs..."
# Replace the simple on: format with branch-filtered format
sed -i '/^on:/,/^jobs:/c\
on:\
  push:\
    branches:\
      - main\
  pull_request:\
concurrency:\
  group: ${{ github.workflow }}-${{ github.ref }}\
  cancel-in-progress: true' .github/workflows/haskell-ci.yml

