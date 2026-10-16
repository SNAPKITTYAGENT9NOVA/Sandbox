#!/usr/bin/env bash
# LEAN-M2-CC-001 MathIR v1: build the GENERATED code with the locked toolchain and run
#   1. the generic differential test (every translated function vs Lean), and
#   2. the acceptance test: SLICE-001's own driver and 2,511 cases against the GENERATED firstKindTerm.
# Runs INSIDE the AArch64 workstation image.
# usage: run.sh <repo-lean-m2-dir> <generated-dir> <slice001-vectors-dir> <out-dir>
set -euo pipefail
L="$(cd "$1" && pwd)"; G="$(cd "$2" && pwd)"; V="$(cd "$3" && pwd)"; OUT="$4"
mkdir -p "$OUT"; OUT="$(cd "$OUT" && pwd)"
R="$L/g3/gen/runtime"; A="$L/g3/gen/acceptance"; S="$L/g3/slice001"
: > "$OUT/build.log"
log() { printf '%s\n' "$*" | tee -a "$OUT/build.log"; }
run() { log "\$ $*"; "$@" 2>&1 | tee -a "$OUT/build.log"; }

log "== toolchain"
{ uname -m; ccomp -version; gm2 --version | head -1; } 2>&1 | tee -a "$OUT/build.log"
[ "$(uname -m)" = aarch64 ] || { log "BLOCKED: not aarch64"; exit 1; }

log "== CompCert: generated C + reference vectors"
run ccomp -I"$R" -I"$G" -c "$G/lm2_gen.c" -o "$OUT/lm2_gen.o"
run ccomp -c "$G/lm2_gen_cases.c" -o "$OUT/lm2_gen_cases.o"

log "== gm2: runtime + generated native Modula-2"
run gm2 -fiso -I"$R" -I"$G" -c "$R/LM2Nat.mod" -o "$OUT/LM2Nat.o"
run gm2 -fiso -I"$R" -I"$G" -c "$R/LM2Wide.mod" -o "$OUT/LM2Wide.o"
run gm2 -fiso -I"$R" -I"$G" -c "$G/LM2Gen.mod" -o "$OUT/LM2Gen.o"
run gm2 -fiso -I"$R" -I"$G" "$R/GenTest.mod" "$OUT/LM2Gen.o" "$OUT/LM2Wide.o" "$OUT/LM2Nat.o" "$OUT/lm2_gen.o" "$OUT/lm2_gen_cases.o" -o "$OUT/gen-test"

log "== acceptance build: SLICE-001 driver against the generated firstKindTerm"
run ccomp -I"$G" -c "$A/lm2_cunningham_adapter.c" -o "$OUT/adapter.o"
run ccomp -c "$V/lm2_cases.c" -o "$OUT/slice001_cases.o"
run gm2 -fiso -I"$A" -I"$G" -I"$R" -c "$A/CunninghamChain.mod" -o "$OUT/CunninghamChainAdapter.o"
run gm2 -fiso -I"$A" -I"$S/m2" -I"$G" -I"$R" "$S/m2/Slice001Test.mod" \
    "$OUT/CunninghamChainAdapter.o" "$OUT/LM2Gen.o" "$OUT/LM2Wide.o" "$OUT/LM2Nat.o" "$OUT/lm2_gen.o" "$OUT/adapter.o" "$OUT/slice001_cases.o" \
    -o "$OUT/acceptance-test"

log "== object checks"
for o in lm2_gen.o lm2_gen_cases.o LM2Nat.o LM2Wide.o LM2Gen.o gen-test acceptance-test; do
  m=$(readelf -h "$OUT/$o" | awk -F: '/Machine:/{gsub(/^ +/,"",$2); print $2}')
  log "$o machine=$m sha256=$(sha256sum "$OUT/$o" | cut -d' ' -f1)"
  [ "$m" = AArch64 ] || { log "BLOCKED: $o is not AArch64"; exit 1; }
done

log "== generic differential test"
set +e; "$OUT/gen-test" > "$OUT/gen-test.log" 2>&1; g=$?; set -e
cat "$OUT/gen-test.log" | tee -a "$OUT/build.log"; log "gen-test exit=$g"
log "== acceptance test (SLICE-001 cases, generated code)"
set +e; "$OUT/acceptance-test" > "$OUT/acceptance.log" 2>&1; a=$?; set -e
cat "$OUT/acceptance.log" | tee -a "$OUT/build.log"; log "acceptance exit=$a"
[ $g -eq 0 ] && [ $a -eq 0 ]
