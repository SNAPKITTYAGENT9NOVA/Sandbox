#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-only
# Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project)
# Local build check run by .githooks/pre-push before every push: the checks CI runs first,
# with the same Lean version, so a change that cannot compile never reaches CI. Fail-closed:
# a missing required tool is a failure, not a skip. Optional tools (gm2) are reported as SKIP.
#   LEAN=/path/to/lean ./build.sh      (default: lean on PATH)
set -uo pipefail
cd "$(dirname "$0")"
LEAN="${LEAN:-$(command -v lean || true)}"
fail=0; tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
ok()   { echo "PASS  $1"; }
bad()  { echo "FAIL  $1"; [ -n "${2:-}" ] && sed 's/^/      /' "$2" | head -40; fail=1; }
skip() { echo "SKIP  $1"; }

# 1. Lean toolchain = the corpus pin (lean-m2/corpus.lock.yaml lean_toolchain)
want=$(awk -F'"' '/^  lean_toolchain:/{print $2; exit}' lean-m2/corpus.lock.yaml); want=${want##*:v}
if [ -z "$LEAN" ] || ! "$LEAN" --version >"$tmp/lv" 2>&1; then bad "lean not found (set LEAN=...)"
elif ! grep -q "version $want," "$tmp/lv"; then bad "lean version: want $want, have $(head -1 "$tmp/lv")"
else ok "lean $want"; fi

# 2. Lean tools: the same compile-and-run-on-nothing checks as CI
if [ $fail -eq 0 ]; then
  { echo "import Lean"; cat lean-m2/tools/mathir_body.lean; } > "$tmp/MathIR.lean"; : > "$tmp/empty.tsv"
  if MATHIR_OUT="$tmp/mout" MATHIR_MODS="$tmp/empty.tsv" "$LEAN" "$tmp/MathIR.lean" > "$tmp/m.log" 2>&1
  then ok "mathir_body.lean (compile + empty run)"; else grep -n error "$tmp/m.log" > "$tmp/m.err"; bad "mathir_body.lean" "$tmp/m.err"; fi
  { echo "import Lean"; cat lean-m2/tools/g2_ledger_body.lean; } > "$tmp/Ledger.lean"
  if LEDGER_OUT="$tmp/ledger.jsonl" LEDGER_MODS="$tmp/empty.tsv" "$LEAN" "$tmp/Ledger.lean" > "$tmp/l.log" 2>&1
  then ok "g2_ledger_body.lean (compile + empty run)"; else grep -n error "$tmp/l.log" > "$tmp/l.err"; bad "g2_ledger_body.lean" "$tmp/l.err"; fi
  if "$LEAN" lean-m2/tools/G1Inventory.lean > "$tmp/g1.log" 2>&1
  then ok "G1Inventory.lean (compile)"; else grep -n error "$tmp/g1.log" > "$tmp/g1.err"; bad "G1Inventory.lean" "$tmp/g1.err"; fi
fi

# 2b. End-to-end on the fixture: generate, check IR against Lean, compile the C, run every case
if [ $fail -eq 0 ]; then
  T=lean-m2/tools/test; E="$tmp/e2e"; mkdir -p "$E/out"; cp "$T/TestDefs.lean" "$E/"
  LIB="$(dirname "$(dirname "$LEAN")")/lib/lean"; printf 'x\tTestDefs\n' > "$E/mods.tsv"
  { echo "import Lean"; echo "import TestDefs"; cat lean-m2/tools/mathir_body.lean; } > "$E/MathIR.lean"
  if ( cd "$E" && "$LEAN" -o TestDefs.olean TestDefs.lean && LEAN_PATH="$E:$LIB" MATHIR_OUT="$E/out" \
       MATHIR_MODS="$E/mods.tsv" "$LEAN" MathIR.lean ) > "$E/run.log" 2>&1; then
    if diff -u "$T/report.golden" "$E/out/report.txt" > "$E/diff.txt"; then ok "fixture: translation and Lean fidelity match report.golden"
    else bad "fixture report differs from report.golden" "$E/diff.txt"; fi
    if gcc -std=c99 -O1 -w -Ilean-m2/g3/gen/runtime -I"$E/out" "$T/ctest.c" "$E/out/lm2_gen.c" "$E/out/lm2_gen_cases.c" -o "$E/ctest" 2> "$E/cc.err" &&
       "$E/ctest" > "$E/ctest.log"; then ok "fixture: generated C $(cat "$E/ctest.log")"
    else cat "$E/cc.err" >> "$E/ctest.log" 2>/dev/null; bad "fixture: generated C" "$E/ctest.log"; fi
  else grep -n error "$E/run.log" > "$E/run.err"; bad "fixture: generator run" "$E/run.err"; fi
fi

# 3. C runtimes and hand-written C: strict C99, warnings are errors
CC="${CC:-$(command -v gcc || command -v cc || true)}"
if [ -z "$CC" ]; then bad "no C compiler"; else
  printf '#include "lm2_nat.h"\n#include "lm2_wide.h"\nint main(void){return 0;}\n' > "$tmp/rt.c"
  if "$CC" -std=c99 -Wall -Wextra -Werror -Wno-unused-function -Ilean-m2/g3/gen/runtime -c "$tmp/rt.c" -o "$tmp/rt.o" 2> "$tmp/c.err"
  then ok "lm2_nat.h + lm2_wide.h (C99 -Werror)"; else bad "C runtimes" "$tmp/c.err"; fi
  if "$CC" -std=c99 -Wall -Werror -Ilean-m2/g3/gen/runtime -c lean-m2/g3/slice001/c/lm2_cunningham.c -o "$tmp/s.o" 2> "$tmp/s.err"
  then ok "slice001 C"; else bad "slice001 C" "$tmp/s.err"; fi
fi

# 4. Modula-2 runtimes (gm2 is optional locally; CI always builds them)
if command -v gm2 >/dev/null; then
  ( cd "$tmp" && cp "$OLDPWD"/lean-m2/g3/gen/runtime/LM2*.def "$OLDPWD"/lean-m2/g3/gen/runtime/LM2*.mod . &&
    gm2 -fiso -c LM2Nat.mod && gm2 -fiso -c LM2Wide.mod ) > "$tmp/gm2.err" 2>&1 && ok "LM2Nat / LM2Wide (gm2)" || bad "Modula-2 runtimes" "$tmp/gm2.err"
else skip "Modula-2 runtimes (gm2 not installed; CI builds them)"; fi

# 5. Python, shell, YAML
for f in $(git ls-files '*.py'); do python3 -m py_compile "$f" 2> "$tmp/py.err" || bad "python $f" "$tmp/py.err"; done; ok "python syntax"
for f in $(git ls-files '*.sh') .githooks/pre-push; do bash -n "$f" 2> "$tmp/sh.err" || bad "shell $f" "$tmp/sh.err"; done; ok "shell syntax"
python3 - $(git ls-files '*.yml' '*.yaml') > "$tmp/y.err" 2>&1 <<'PY' && ok "YAML" || bad "YAML" "$tmp/y.err"
import sys, yaml
for f in sys.argv[1:]: yaml.safe_load(open(f))
PY

[ $fail -eq 0 ] && echo "BUILD CHECK PASS" || echo "BUILD CHECK FAIL"
exit $fail
