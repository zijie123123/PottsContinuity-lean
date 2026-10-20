#!/usr/bin/env bash
# Download arXiv:1505.04159v1 into paper/ and compare it with the arXiv PDF recorded in paper/README.md.
set -euo pipefail
cd "$(dirname "$0")/.."
expected=7d2934e489afb571136b67ea887bea85835276ad3d80e9999343d05b7d9c1c99
out=paper/1505.04159v1.pdf
curl -fL --retry 3 -o "$out" https://arxiv.org/pdf/1505.04159v1
if command -v sha256sum >/dev/null; then actual=$(sha256sum "$out" | cut -d' ' -f1)
else actual=$(shasum -a 256 "$out" | cut -d' ' -f1); fi
if [ "$actual" = "$expected" ]; then
  echo "OK: $out matches the arXiv PDF recorded in paper/README.md"
else
  echo "WARNING: $out has SHA-256 $actual, expected $expected (arXiv may have regenerated the PDF)" >&2
  exit 1
fi
