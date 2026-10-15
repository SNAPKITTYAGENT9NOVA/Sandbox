#!/usr/bin/env bash
# LEAN-M2-CC-001 SLICE-001: build with the locked toolchain and run the differential test.
# Runs INSIDE the AArch64 workstation image (CompCert 3.18 + gm2).
# usage: run.sh <slice-dir> <lm2_cases.c from Spec.lean> <out-dir>
set -euo pipefail
S="$(cd "$1" && pwd)"; CASES="$2"; OUT="$3"
mkdir -p "$OUT"; OUT="$(cd "$OUT" && pwd)"
log() { printf '%s\n' "$*" | tee -a "$OUT/build.log"; }
: > "$OUT/build.log"

log "== toolchain"
{ uname -m; ccomp -version; gm2 --version | head -1; gm2 -dumpmachine; } 2>&1 | tee -a "$OUT/build.log"
[ "$(uname -m)" = aarch64 ] || { log "BLOCKED: not aarch64"; exit 1; }

log "== CompCert (ccomp is the only C compiler used)"
ccomp -I"$S/c" -c "$S/c/lm2_cunningham.c" -o "$OUT/lm2_cunningham.o" 2>&1 | tee -a "$OUT/build.log"
ccomp -c "$CASES" -o "$OUT/lm2_cases.o" 2>&1 | tee -a "$OUT/build.log"

log "== GNU Modula-2 (ISO)"
gm2 -fiso -I"$S/m2" -c "$S/m2/CunninghamChain.mod" -o "$OUT/CunninghamChain.o" 2>&1 | tee -a "$OUT/build.log"
gm2 -fiso -I"$S/m2" "$S/m2/Slice001Test.mod" \
    "$OUT/CunninghamChain.o" "$OUT/lm2_cunningham.o" "$OUT/lm2_cases.o" \
    -o "$OUT/slice001-test" 2>&1 | tee -a "$OUT/build.log"

log "== object checks"
for o in lm2_cunningham.o lm2_cases.o CunninghamChain.o slice001-test; do
  m=$(readelf -h "$OUT/$o" | awk -F: '/Machine:/{gsub(/^ +/,"",$2); print $2}')
  log "$o machine=$m sha256=$(sha256sum "$OUT/$o" | cut -d' ' -f1)"
  [ "$m" = AArch64 ] || { log "BLOCKED: $o is not AArch64"; exit 1; }
done
log "lm2_cases.c sha256=$(sha256sum "$CASES" | cut -d' ' -f1)"

log "== differential test"
set +e
"$OUT/slice001-test" > "$OUT/test.log" 2>&1
rc=$?
set -e
cat "$OUT/test.log" | tee -a "$OUT/build.log"
log "test exit=$rc"
exit $rc
