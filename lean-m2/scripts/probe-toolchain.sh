#!/usr/bin/env bash
# LEAN-M2-CC-001 · G0 probe-toolchain
#
# Usage:
#   probe-toolchain.sh <lean-project-root>     full G0 (toolchain + project pins + corpus)
#   probe-toolchain.sh --toolchain-only        toolchain only; corpus recorded NOT_EVALUATED
#
# Environment:
#   OUT                       output dir (default: build/toolchain)
#   LEAN_M2_EXECUTION         native | emulated   (set by the workstation launcher; required)
#   LEAN_M2_ALLOW_EMULATION   1 to accept QEMU-emulated AArch64 (puts QEMU in the trusted base)
#
# Fail-closed: every check writes PASS / BLOCKED / NOT_EVALUATED to checks.tsv.
# Overall status:
#   PASS                  every check passed (full mode only)
#   TOOLCHAIN_ONLY_PASS   toolchain checks passed; corpus deliberately not evaluated
#   BLOCKED               anything else (exit 1)
# Never substitutes another compiler or target. A PASS here is G0 only; it certifies nothing downstream.
set -uo pipefail

MODE=full; PROJECT_ROOT=""
case "${1:-}" in
  --toolchain-only) MODE=toolchain-only ;;
  "") ;;
  *) PROJECT_ROOT="$1" ;;
esac

HERE="$(cd "$(dirname "$0")" && pwd)"
FX="$(cd "${FX:-$HERE/../fixtures/abi}" && pwd)"
OUT="${OUT:-build/toolchain}"
mkdir -p "$OUT"; OUT="$(cd "$OUT" && pwd)"
: > "$OUT/checks.tsv"

rec()  { printf '%s\t%s\t%s\n' "$1" "$2" "$3" >> "$OUT/checks.tsv"; }
pass() { rec PASS "$1" "$2"; }
blk()  { rec BLOCKED "$1" "$2"; }
have() { command -v "$1" >/dev/null 2>&1; }
run()  { # name cmd... : capture combined output, record exit status
  local n="$1"; shift
  if "$@" > "$OUT/$n.log" 2>&1; then pass "$n" "$*"; return 0
  else local rc=$?; blk "$n" "exit=$rc: $*"; return 1; fi
}

# ---------- host / execution ----------
ARCH="$(uname -m)"; echo "$ARCH" > "$OUT/arch.txt"
[ "$ARCH" = aarch64 ] && pass arch aarch64 \
  || blk arch "uname -m = $ARCH; contract requires AArch64 Linux (no x86-64 substitution)"
[ "$(uname -s)" = Linux ] && pass os Linux || blk os "uname -s = $(uname -s)"

EXECUTION="${LEAN_M2_EXECUTION:-}"
case "$EXECUTION" in
  native)   pass execution native ;;
  emulated) if [ "${LEAN_M2_ALLOW_EMULATION:-0}" = 1 ]; then
              pass execution "emulated (QEMU accepted into trusted base by LEAN_M2_ALLOW_EMULATION=1)"
            else
              blk execution "emulated AArch64 not accepted; set LEAN_M2_ALLOW_EMULATION=1 to opt in"
            fi ;;
  *)        blk execution "LEAN_M2_EXECUTION not declared (native|emulated)" ;;
esac

# ---------- required executables ----------
for t in lean lake ccomp gm2 sha256sum readelf; do
  if p="$(command -v "$t")"; then pass "exe:$t" "$p"; else blk "exe:$t" "not on PATH"; fi
done

# Lean versions are resolved per project by elan; run inside the project when one is given.
if have lean && have lake; then
  if [ -n "$PROJECT_ROOT" ]; then
    ( cd "$PROJECT_ROOT" && lean --version ) > "$OUT/lean-version.log" 2>&1 \
      && pass lean-version "$(head -1 "$OUT/lean-version.log")" || blk lean-version "lean --version failed in project"
    ( cd "$PROJECT_ROOT" && lake --version ) > "$OUT/lake-version.log" 2>&1 \
      && pass lake-version "$(head -1 "$OUT/lake-version.log")" || blk lake-version "lake --version failed in project"
  else
    rec NOT_EVALUATED lean-version "resolved per project by lean-toolchain; no project given"
  fi
fi

# ---------- CompCert ----------
if have ccomp; then
  run compcert-version ccomp -version
  grep -Eq '(^|[^0-9.])3\.18([^0-9]|$)' "$OUT/compcert-version.log" \
    && pass compcert-3.18 "exact token 3.18" || blk compcert-3.18 "observed version is not 3.18"
  # Configured target comes from the installed configuration file, not the version banner.
  CCROOT="$(cd "$(dirname "$(command -v ccomp)")/.." && pwd)"
  INI="$(find "$CCROOT" -name compcert.ini 2>/dev/null | head -1)"
  if [ -n "$INI" ]; then
    cp "$INI" "$OUT/compcert.ini"
    pass compcert-config "$(sha256sum "$INI" | cut -d' ' -f1) $INI"
    grep -Eq '^arch=aarch64$'  "$INI" && pass compcert-arch aarch64 || blk compcert-arch "compcert.ini arch != aarch64"
    grep -Eq '^system=linux$'  "$INI" && pass compcert-system linux || blk compcert-system "compcert.ini system != linux"
  else
    blk compcert-config "compcert.ini not found under $CCROOT"
  fi
  [ -f /opt/lean-m2/compcert-source.txt ] && cp /opt/lean-m2/compcert-source.txt "$OUT/"
fi

# ---------- GNU Modula-2 ----------
if have gm2; then
  run gm2-version gm2 --version
  gm2 -dumpmachine > "$OUT/gm2-target.txt" 2>&1
  grep -Eq '^aarch64-.*linux' "$OUT/gm2-target.txt" \
    && pass gm2-target "$(cat "$OUT/gm2-target.txt")" || blk gm2-target "gm2 -dumpmachine is not aarch64-*-linux*"
fi

# ---------- compile fixtures, check ELF machine of both objects ----------
if have gm2 && have ccomp && have readelf; then
  W="$OUT/abi"; mkdir -p "$W"
  run cc-compile  ccomp -c "$FX/abi_probe_c.c" -o "$W/abi_probe_c.o"
  run gm2-compile gm2 -fiso -I"$FX" -c "$FX/AbiProbe.mod" -o "$W/AbiProbe.o"
  for o in abi_probe_c.o AbiProbe.o; do
    [ -f "$W/$o" ] || continue
    readelf -h "$W/$o" > "$W/$o.readelf.txt"
    grep -Eq 'Machine:[[:space:]]+AArch64' "$W/$o.readelf.txt" \
      && pass "elf:$o" "AArch64 $(sha256sum "$W/$o" | cut -d' ' -f1)" || blk "elf:$o" "ELF machine is not AArch64"
  done

  # ---------- linked + runtime ABI probe (both call directions) ----------
  if [ -f "$W/abi_probe_c.o" ] && [ -f "$W/AbiProbe.o" ]; then
    if run abi-link gm2 -fiso -I"$FX" "$FX/AbiLinkProbe.mod" "$W/AbiProbe.o" "$W/abi_probe_c.o" -o "$W/abi-link-probe"; then
      if "$W/abi-link-probe" > "$OUT/abi-runtime.log" 2>&1; then
        pass abi-runtime "$(tail -1 "$OUT/abi-runtime.log")"
      else
        blk abi-runtime "see abi-runtime.log: $(grep -c FAIL "$OUT/abi-runtime.log") failing checks"
      fi
    fi
  fi
fi

# ---------- project pins + corpus ----------
if [ "$MODE" = toolchain-only ]; then
  rec NOT_EVALUATED corpus "--toolchain-only"
elif [ -z "$PROJECT_ROOT" ]; then
  blk corpus "no project root (usage: probe-toolchain.sh <lean-project-root> | --toolchain-only)"
else
  for f in lean-toolchain lake-manifest.json; do
    [ -s "$PROJECT_ROOT/$f" ] && pass "pin:$f" "$(sha256sum "$PROJECT_ROOT/$f" | cut -d' ' -f1)" \
      || blk "pin:$f" "missing or empty in $PROJECT_ROOT"
  done
  n=$(find "$PROJECT_ROOT" -name '*.lean' -not -path '*/.lake/*' | wc -l)
  [ "$n" -gt 0 ] && pass corpus "$n .lean files (excluding .lake/)" || blk corpus "0 .lean files under $PROJECT_ROOT"
fi

# ---------- executable fingerprints ----------
for t in lean lake ccomp gm2; do
  have "$t" && sha256sum "$(readlink -f "$(command -v "$t")")"
done > "$OUT/executable-hashes.txt"

# ---------- machine-readable result ----------
python3 - "$OUT" "$MODE" <<'PY'
import json, sys, datetime, platform
out, mode = sys.argv[1], sys.argv[2]
rows = [l.rstrip("\n").split("\t", 2) for l in open(f"{out}/checks.tsv") if l.strip()]
checks = [{"status": s, "check": c, "detail": d} for s, c, d in rows]
st = {c["status"] for c in checks}
if "BLOCKED" in st:            status = "BLOCKED"
elif "NOT_EVALUATED" in st:    status = "TOOLCHAIN_ONLY_PASS" if mode == "toolchain-only" else "BLOCKED"
else:                          status = "PASS"
json.dump({
  "contract": "LEAN-M2-CC-001", "gate": "G0", "mode": mode, "status": status,
  "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
  "host": {"machine": platform.machine(), "kernel": platform.release()},
  "checks": checks,
  "scope_note": "G0 evidence only. Says nothing about extraction correctness, Lean proofs, or G1-G6.",
}, open(f"{out}/g0-result.json", "w"), indent=2, sort_keys=True)
print(status)
PY
python3 -c 'import json,sys; sys.exit(0 if json.load(open(sys.argv[1]))["status"] in ("PASS","TOOLCHAIN_ONLY_PASS") else 1)' "$OUT/g0-result.json"
