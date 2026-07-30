#!/usr/bin/env bash
# Confirms that _CoqProject lists every rocq/*.v file exactly once, and
# that no file is missing or listed twice.
set -euo pipefail
cd "$(dirname "$0")/.."

actual=$(find rocq -name '*.v' | sort)
listed=$(grep '^rocq/' _CoqProject | sort)

if [ "$actual" != "$listed" ]; then
  echo "MISMATCH between rocq/*.v on disk and _CoqProject:"
  diff <(echo "$actual") <(echo "$listed") || true
  exit 1
fi

dupes=$(echo "$listed" | uniq -d)
if [ -n "$dupes" ]; then
  echo "Duplicate entries in _CoqProject:"
  echo "$dupes"
  exit 1
fi

count=$(echo "$actual" | wc -l)
echo "Source inventory OK: $count file(s) in rocq/, each listed exactly once in _CoqProject."
