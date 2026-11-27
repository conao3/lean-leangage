#!/bin/sh
set -eu

if [ $# -ne 1 ]; then
  echo "usage: $0 <directory>" >&2
  exit 2
fi

revision=$(sed -n 's|.*"github:conao3/lean-leanfran/\([0-9a-f]\{40\}\)".*|\1|p' "$(dirname "$0")/../flake.nix")
if [ -z "$revision" ]; then
  echo "flake.nix names no commit of lean-leanfran" >&2
  exit 1
fi

mkdir -p "$1/src" "$1/bin"
cd "$1"
git -C src init --quiet
git -C src fetch --quiet --depth 1 https://github.com/conao3/lean-leanfran.git "$revision"
git -C src checkout --quiet FETCH_HEAD
for pair in Rust:leanfran Python:leanfran-python Go:leanfran-go; do
  (cd "src/langs/${pair%%:*}" && lake build "${pair##*:}")
  ln -sf "$PWD/src/langs/${pair%%:*}/.lake/build/bin/${pair##*:}" "bin/${pair##*:}"
done
