<!-- SPDX-License-Identifier: AGPL-3.0-only -->
<!-- Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) -->
# SLICE-001: `CunninghamChain.firstKindTerm`

This is the first vertical slice of LEAN-M2-CC-001 (contract §14): one computational definition
taken through Lean → C subset → CompCert → Modula-2 → differential test. This document is the
**semantic contract**.

> **Status: built and passing** (CI run 38686128245): `LEAN_VERIFIED + SEMANTICALLY_MAPPED + DIFFERENTIALLY_TESTED`.
> - All claims below are discharged in Lean.
> - 2,511 cases, 0 failures for both the CompCert C and the native Modula-2, on native AArch64.
>
> Evidence: `slice001/LEDGER.json`. Code: `slice001/`.

## Source

| | |
|---|---|
| Declaration | `CunninghamChain.firstKindTerm` |
| Module | `FormalConjectures.Arxiv.«1104.1579».CunninghamChain` |
| File | `FormalConjectures/Arxiv/1104.1579/CunninghamChain.lean`, sha256 `64ba20bf6ffa5aaf9fe300922a7b6591cca280a8ff8b05d62a6f04c3c69988e2` |
| Corpus | google-deepmind/formal-conjectures @ `84cf7f8` (Lean 4.33.1) |

```lean
/-- The `n`th term generated from `p` by the first-kind recurrence `q ↦ 2q + 1`. -/
def firstKindTerm (p : ℕ) : ℕ → ℕ
  | 0     => p
  | n + 1 => 2 * firstKindTerm p n + 1
```

## Verified facts (with evidence)

- **`LEAN_VERIFIED`:** a kernel-checked `def` whose transitive axioms lie within {`propext`, `Classical.choice`, `Quot.sound`}. It is `safe` and computable, with no `extern` or `implemented_by`. Evidence: it appears in the G3 exact-domain candidate list of G2 run 38677197622, and that list requires all of these properties.
- **Type:** `ℕ → ℕ → ℕ`. Its only type constant is `Nat`, so it lies in the exact domain.
- **Reference values from the corpus:** the test theorem `two_starts_firstKind_length_five` (category `test`, proved by `norm_num`) evaluates `firstKindTerm 2 i` for i = 0..5. That gives the reference values 2, 5, 11, 23, 47, 95.

## Claims discharged in this slice (`slice001/Spec.lean`)

1. **Closed form** `firstKindTerm p n = 2^n * (p + 1) - 1`.
   - By hand: t₀ + 1 = p + 1, and tₙ₊₁ + 1 = 2(tₙ + 1).
   - To be proved as a Lean lemma in this repository. It must not be assumed.
2. **Bounded iteration:** tₙ ≥ 2ⁿ − 1 for every p. By claim 1, the result fits in 64 bits iff 2ⁿ(p + 1) ≤ 2⁶⁴.
   - So n = 64 is representable **only** for p = 0 (the result is exactly 2⁶⁴ − 1).
   - Every n ≥ 65 overflows for every p.
   - The machine loops therefore run at most 64 iterations.

   Both facts are to be proved in Lean.

## Semantic domains

Lean computes on unbounded ℕ and is **total**. The machine implementations compute on 64-bit
unsigned integers and are **partial**. The mapping is:

| Input | Lean | Machine |
|---|---|---|
| `p, n` | any ℕ | `uint64_t` / `LONGCARD` (8 bytes, width verified by the G0 ABI probe) |
| result ≤ 2⁶⁴−1 | `firstKindTerm p n` | same value, status `OK` |
| result > 2⁶⁴−1 | `firstKindTerm p n` | **no value**, status `OVERFLOW`. Never wraps, never truncates |

Representability condition: `2^n * (p + 1) ≤ 2^64`, which is equivalent to the result being ≤ 2⁶⁴−1 by claim 1.
Machine equality is exact integer equality. There is no floating point.

## Interfaces (ABI rules from G0: scalars and caller-owned out-pointers only, no aggregates by value)

**C subset (compiled only by CompCert 3.18, target `aarch64-linux`):**
```c
/* 0 = OK (*out set), 1 = OVERFLOW (*out untouched), -1 = NULL out */
int32_t lm2_cunningham_first_kind_term(uint64_t p, uint64_t n, uint64_t *out);
```
The implementation iterates `t := 2t + 1`, checking `t > (UINT64_MAX - 1) / 2` before each step.
`n ≥ 65` short-circuits to `OVERFLOW`, by claim 2. The boundary cases (n = 64, p = 0) and (n = 64, p = 1) are mandatory tests.

**Modula-2 (gm2, ISO dialect):** two separately tested artifacts, which are never conflated.
- `CunninghamChain.def/.mod`: a **native** Modula-2 implementation of the same recurrence (hand-written for this slice; to be produced by the MathIR generator later), with `LONGCARD` and an explicit `Status` result.
- `cunningham_c.def` (`DEFINITION MODULE FOR "C"`, with `EXPORT UNQUALIFIED`): a **binding** to the CompCert object.

## Differential tests (G6 for this slice)

- **Reference:** Lean evaluates `firstKindTerm` exactly on ℕ. Each case is classified `OK` or `OVERFLOW` by comparing the Lean value with 2⁶⁴−1, also in Lean.
- **Grid:** p ∈ {0, 1, 2, 3, 2³²−1, 2⁶³−1, 2⁶⁴−1} × n ∈ {0..70}. This covers the exact boundary: (64, 0) is `OK` with value 2⁶⁴−1, and (64, 1) and (65, 0) are `OVERFLOW`.
- **Randomized:** p and n with a recorded seed.
- **Corpus anchors:** the values 2, 5, 11, 23, 47, 95.
- **Comparison:** C (via CompCert), native Modula-2, and Modula-2 → C binding must all match Lean exactly, in both value and status.
- **Status ceiling:** a pass yields `DIFFERENTIALLY_TESTED` only. `FORMALLY_EQUIVALENT` is **not** claimed by this slice.

## Exit criteria

1. The Lean lemmas for claims 1 and 2 are kernel-checked.
2. `ccomp` compiles the C under the locked configuration, and the object is AArch64 ELF.
3. gm2 compiles the native module and the binding, and both link on native AArch64.
4. All differential cases agree. The results are recorded with seeds, versions and hashes.
5. A ledger row records `LEAN_VERIFIED + SEMANTICALLY_MAPPED + DIFFERENTIALLY_TESTED`.
