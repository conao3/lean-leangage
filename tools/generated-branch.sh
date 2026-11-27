#!/bin/sh
set -eu

if [ -n "$(git status --porcelain)" ]; then
  echo "the working tree differs from HEAD: commit or remove the changes first" >&2
  exit 1
fi

head=$(git rev-parse HEAD)
message="Generate from $(git rev-parse --short "$head")"

index=$(mktemp -u)
trap 'rm -f "$index"' EXIT
GIT_INDEX_FILE="$index" git read-tree "$head"
GIT_INDEX_FILE="$index" git add --force -- "$@"
tree=$(GIT_INDEX_FILE="$index" git write-tree)

if git fetch --quiet origin '+refs/heads/generated:refs/remotes/origin/generated' 2>/dev/null; then
  commit=$(git commit-tree "$tree" -p "$(git rev-parse origin/generated)" -p "$head" -m "$message")
else
  commit=$(git commit-tree "$tree" -p "$head" -m "$message")
fi
git push origin "$commit:refs/heads/generated"
echo "generated: $commit (from $head)"
