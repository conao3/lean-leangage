#!/bin/sh
set -eu

if [ $# -ne 1 ]; then
  echo "usage: $0 <version>" >&2
  exit 2
fi

version=$1
cd "$(dirname "$0")/.."

sed -i "0,/^version = \".*\"/s//version = \"$version\"/" langs/rust/Cargo.toml samples/rust/Cargo.toml
sed -i "s|^leangage = { path = \"../leangage\", version = \".*\" }|leangage = { path = \"../leangage\", version = \"$version\" }|" langs/rust/leangage-pg/Cargo.toml
sed -i "0,/^            version = \".*\";/s//            version = \"$version\";/" flake.nix
(cd langs/rust && cargo update --workspace)
(cd samples/rust && cargo update --workspace)
(cd langs/python && uv version "$version" --no-sync)
(cd samples/python && uv version "$version" --no-sync)

for file in langs/rust/Cargo.toml langs/rust/leangage-pg/Cargo.toml langs/rust/Cargo.lock \
  samples/rust/Cargo.toml samples/rust/Cargo.lock flake.nix langs/python/pyproject.toml \
  langs/python/uv.lock samples/python/pyproject.toml samples/python/uv.lock; do
  if ! grep -q "\"$version\"" "$file"; then
    echo "$file does not name $version" >&2
    exit 1
  fi
done
