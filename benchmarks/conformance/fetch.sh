#!/bin/sh
# Fetch Taffy's browser-generated layout fixtures at a pinned revision into
# target/taffy-fixtures. tests/conformance reads them from there, or from
# $KERU_CONFORMANCE_DIR.
set -eu
REV=4e59968eda29ceeb0bbaeb3993c8cd38baa3d0a6
root=$(cd "$(dirname "$0")/../.." && pwd)
dest="$root/target/taffy-fixtures"
if [ -d "$dest/.git" ] && [ "$(git -C "$dest" rev-parse HEAD)" = "$REV" ]; then
  echo "fixtures already at $REV"
  exit 0
fi
rm -rf "$dest"
git init -q "$dest"
git -C "$dest" remote add origin https://github.com/DioxusLabs/taffy.git
git -C "$dest" fetch -q --depth 1 origin "$REV"
git -C "$dest" checkout -q FETCH_HEAD
echo "fetched Taffy fixtures at $REV into $dest"
