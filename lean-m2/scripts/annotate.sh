#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-only
# Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project)
# Publish text as GitHub check-run annotations (readable via the REST API, unlike job logs).
# usage: annotate.sh <notice|warning|error> <title> <file> [max-lines]
# GitHub truncates an annotation message at about 4 KB, so longer text is split at line
# boundaries into parts titled "<title> (i/n)". GitHub also keeps a limited number of
# annotations per step (10 per level), so keep evidence compact.
set -uo pipefail
level="$1"; title="$2"; file="$3"; max="${4:-60}"
[ -f "$file" ] || { echo "::$level title=$title::(missing: $file)"; exit 0; }
limit=3000
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
tail -n "$max" "$file" | cut -c1-300 | LC_ALL=C awk -v lim="$limit" -v dir="$tmp" '
  { len = length($0) + 1
    if (n == 0 || size + len > lim) { n++; size = 0 }
    print > (dir "/part" sprintf("%04d", n)); size += len }'
parts=("$tmp"/part*)
[ -e "${parts[0]}" ] || { echo "::$level title=$title::(empty)"; exit 0; }
total=${#parts[@]}
i=0
for p in "${parts[@]}"; do
  i=$((i + 1))
  t="$title"; [ "$total" -gt 1 ] && t="$title ($i/$total)"
  msg="$(cat "$p")"
  msg="${msg//'%'/'%25'}"; msg="${msg//$'\r'/'%0D'}"; msg="${msg//$'\n'/'%0A'}"
  echo "::$level title=$t::$msg"
done
