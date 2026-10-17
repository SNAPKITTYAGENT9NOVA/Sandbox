<!-- SPDX-License-Identifier: AGPL-3.0-only -->
<!-- Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) -->
# LEAN-M2-CC-001 release package

Natural-number functions from the Lean 4 corpus
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(frozen commit in `evidence/corpus.lock.yaml`), translated by the MathIR generator into
**CompCert C** and **native Modula-2**, built for **AArch64 Linux**.
`MANIFEST.json` lists every file with its SHA-256, the source commit, the CI run that built and
gated this package, the coverage, and what is and is not claimed.

## Contents

| Path | What |
|---|---|
| `include/lm2_gen.h` | C prototypes: `int32_t lm2_<name>(uint64_t a0, …, uint64_t *out)` and `LM2_FN_<name>` indices |
| `include/lm2_nat.h`, `include/lm2_wide.h` | checked 64-bit runtime and the exact wide fallback (header-only, CompCert C99) |
| `src/c/lm2_gen.c` | generated C (fast checked path + exact wide fallback per function) |
| `src/m2/` | generated Modula-2 module `LM2Gen` and runtime modules `LM2Nat`, `LM2Wide` (ISO dialect) |
| `lib/aarch64-linux/` | the same code compiled: `lm2_gen.o` by CompCert, `LM2Gen.o` / `LM2Nat.o` / `LM2Wide.o` by gm2 |
| `evidence/` | ledger, IR, per-function report, blocked list, test logs, lockfiles, measured toolchain, gate report |

## Calling convention

Every function returns a status and writes its result through `out` only on success:

| Status | Meaning |
|---|---|
| `LM2_OK` (0) | `*out` holds the exact value of the Lean definition |
| `LM2_OVERFLOW` (1) | the exact value does not fit in 64 bits (or exceeds the 4224-bit exact fallback); `*out` untouched |
| `LM2_ERR_NULL` (-1) | `out` is NULL |

The Modula-2 procedures `LM2Gen.F_<name>(a0, …; VAR out: LONGCARD): INTEGER` follow the same
contract (`LM2Gen.Ok`, `LM2Gen.Overflow`).

## Building against it

    ccomp -I include -c your.c && ccomp your.o lib/aarch64-linux/lm2_gen.o -o app    # C
    gm2 -fiso -I src/m2 your.mod lib/aarch64-linux/LM2Gen.o lib/aarch64-linux/LM2Wide.o lib/aarch64-linux/LM2Nat.o -o app

## What the gate verified before this package was written

See `evidence/gate-report.txt` (every check is listed). In summary: the measured toolchain equals
the frozen lockfile; the corpus gates G1/G2 pass; the IR agrees with Lean's compiled definitions
on every evaluated input; the C and Modula-2 code are sound and complete on every Lean reference
case; SLICE-001's acceptance test passes on the generated code; and every compiled object is
byte-identical to the one recorded in the ledger.

**License:** AGPL-3.0-only (see `LICENSE` and `NOTICE`).

**Not claimed:** formal equivalence. Testing covers finite input sets (see `limits` in the manifest).
