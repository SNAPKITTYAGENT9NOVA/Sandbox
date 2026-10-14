#!/usr/bin/env bash
# Publish text as a GitHub check-run annotation (readable via the REST API, unlike job logs).
# usage: annotate.sh <notice|warning|error> <title> <file> [max-lines]
# GitHub keeps a limited number of annotations per step; keep messages compact.
set -uo pipefail
level="$1"; title="$2"; file="$3"; max="${4:-60}"
[ -f "$file" ] || { echo "::$level title=$title::(missing: $file)"; exit 0; }
msg="$(tail -n "$max" "$file" | cut -c1-300)"
msg="${msg//'%'/'%25'}"; msg="${msg//$'\r'/'%0D'}"; msg="${msg//$'\n'/'%0A'}"
echo "::$level title=$title::$msg"
