#!/bin/sh
set -eu

if [ $# -ne 1 ]; then
  echo "usage: $0 <version>" >&2
  exit 2
fi

version=$1
cd "$(dirname "$0")/.."

sed -i "0,/^version = \".*\"/s//version = \"$version\"/" rust/Cargo.toml
sed -i "s|^leangage = { path = \"../leangage\", version = \".*\" }|leangage = { path = \"../leangage\", version = \"$version\" }|" rust/leangage-pg/Cargo.toml
sed -i "0,/^            version = \".*\";/s//            version = \"$version\";/" flake.nix
(cd rust && cargo update --workspace)
(cd python && uv version "$version" --no-sync)

for file in rust/Cargo.toml rust/leangage-pg/Cargo.toml flake.nix rust/Cargo.lock python/pyproject.toml python/uv.lock; do
  if ! grep -q "\"$version\"" "$file"; then
    echo "$file does not name $version" >&2
    exit 1
  fi
done
