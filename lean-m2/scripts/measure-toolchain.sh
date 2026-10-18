#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-only
# Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project)
# LEAN-M2-CC-001 · measure the native toolchain for toolchain.lock.yaml (fail-closed).
#
# Runs INSIDE the AArch64 workstation image. Prints one `key<TAB>value` line per measured field
# (the keys are dotted paths into toolchain.lock.yaml). Exit 1 if any field cannot be measured;
# no value is ever guessed or defaulted.
#
# usage: measure-toolchain.sh > observed.tsv
set -uo pipefail
fail=0
out() { printf '%s\t%s\n' "$1" "$2"; }
need() { # key value-or-empty description
  if [ -n "$2" ]; then out "$1" "$2"; else echo "BLOCKED: cannot measure $1 ($3)" >&2; fail=1; fi
}
sha() { sha256sum "$1" | cut -d' ' -f1; }

[ "$(uname -m)" = aarch64 ] || { echo "BLOCKED: not aarch64" >&2; exit 1; }

# ---- CompCert ----
CC="$(readlink -f "$(command -v ccomp 2>/dev/null)" 2>/dev/null || true)"
need compcert.compiler_path "$CC" "ccomp not on PATH"
[ -n "$CC" ] && need compcert.compiler_sha256 "$(sha "$CC")" "hash of ccomp"
CCROOT="$(cd "$(dirname "$CC")/.." 2>/dev/null && pwd)"
INI="$(find "$CCROOT" -name compcert.ini 2>/dev/null | head -1)"
need compcert.configuration_sha256 "$( [ -n "$INI" ] && sha "$INI")" "compcert.ini under $CCROOT"
ini() { [ -n "$INI" ] && sed -n "s/^$1=//p" "$INI" | head -1; }
# CompCert delegates preprocessing, assembling and linking to the commands named in compcert.ini;
# record each command and the binary it resolves to, with that binary's hash.
for role in prepro asm linker; do
  cmd="$(ini "$role")"
  bin="$(readlink -f "$(command -v "${cmd%% *}" 2>/dev/null)" 2>/dev/null || true)"
  key=$role; [ "$role" = prepro ] && key=preprocessor; [ "$role" = asm ] && key=assembler
  need "compcert.external_toolchain.$key" "$( [ -n "$cmd" ] && [ -n "$bin" ] && echo "$cmd | $bin | sha256:$(sha "$bin")")" "compcert.ini $role="
done
GCC="$(ini prepro)"; GCC="${GCC%% *}"
need compcert.external_toolchain.sysroot "$( [ -n "$GCC" ] && { s="$("$GCC" -print-sysroot 2>/dev/null)"; echo "${s:-/}"; })" "$GCC -print-sysroot"
need compcert.external_toolchain.target_triple "$( [ -n "$GCC" ] && "$GCC" -dumpmachine 2>/dev/null)" "$GCC -dumpmachine"

# ---- GNU Modula-2 ----
GM2="$(readlink -f "$(command -v gm2 2>/dev/null)" 2>/dev/null || true)"
need modula2.executable_path "$GM2" "gm2 not on PATH"
[ -n "$GM2" ] && need modula2.executable_sha256 "$(sha "$GM2")" "hash of gm2"
LIB="$(gm2 -print-file-name=libm2iso.a 2>/dev/null)"; [ -f "$LIB" ] || LIB=""
need modula2.runtime_library "$( [ -n "$LIB" ] && readlink -f "$LIB")" "gm2 -print-file-name=libm2iso.a"
need modula2.runtime_version "$(gm2 -dumpfullversion 2>/dev/null)" "gm2 -dumpfullversion"
# fingerprint of every Modula-2 runtime archive gm2 links from (sorted name:sha256 list, hashed)
LIBDIR="$( [ -n "$LIB" ] && dirname "$LIB")"
fp="$( [ -n "$LIBDIR" ] && cd "$LIBDIR" && for f in $(ls libm2*.a 2>/dev/null | sort); do echo "$f:$(sha "$f")"; done | sha256sum | cut -d' ' -f1)"
n="$( [ -n "$LIBDIR" ] && ls "$LIBDIR"/libm2*.a 2>/dev/null | wc -l)"
need modula2.standard_library_fingerprint "$( [ "${n:-0}" -gt 0 ] && echo "sha256:$fp over $n libm2*.a in $LIBDIR")" "libm2*.a next to libm2iso.a"

exit $fail
