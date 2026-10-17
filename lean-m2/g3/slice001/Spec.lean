-- SPDX-License-Identifier: AGPL-3.0-only
-- Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project)
/-
LEAN-M2-CC-001 · SLICE-001 · `CunninghamChain.firstKindTerm`

This file is elaborated against the frozen corpus (formal-conjectures @ 84cf7f8, Lean 4.33.1):
    cd <corpus> && SLICE_OUT=<dir> lake env lean <repo>/lean-m2/g3/slice001/Spec.lean

It does two things, both against the corpus's own definition (it is imported, not restated):
  1. proves the facts the machine implementations rely on (see SLICE-001-firstKindTerm.md):
       * closed form          firstKindTerm p n + 1 = 2^n * (p + 1)
       * representability    firstKindTerm p n ≤ 2^64 - 1  ↔  2^n * (p + 1) ≤ 2^64
       * iteration bound      65 ≤ n → 2^64 - 1 < firstKindTerm p n
       * exact boundary       firstKindTerm 0 64 = 2^64 - 1  ∧  2^64 - 1 < firstKindTerm 1 64
     and prints their axioms (CI rejects `sorryAx` and non-standard axioms);
  2. writes the differential-test reference vectors, as C source (`lm2_cases.c`) and JSON Lines.
     Expected values are computed by evaluating the corpus definition on ℕ. For n ≥ 65 the
     expected status OVERFLOW is justified by `overflow_of_ge_65`, so no astronomically large
     value is ever computed.
-/
import FormalConjectures.Arxiv.«1104.1579».CunninghamChain

open CunninghamChain

namespace LeanM2.Slice001

theorem firstKindTerm_succ_eq (p n : ℕ) :
    firstKindTerm p (n + 1) = 2 * firstKindTerm p n + 1 := by
  simp only [firstKindTerm]

/-- Closed form, stated without truncated subtraction. -/
theorem closed_form (p n : ℕ) : firstKindTerm p n + 1 = 2 ^ n * (p + 1) := by
  induction n with
  | zero => simp [firstKindTerm]
  | succ n ih =>
    rw [firstKindTerm_succ_eq, pow_succ]
    calc 2 * firstKindTerm p n + 1 + 1 = 2 * (firstKindTerm p n + 1) := by ring
      _ = 2 * (2 ^ n * (p + 1)) := by rw [ih]
      _ = 2 ^ n * 2 * (p + 1) := by ring

theorem two_pow_64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
theorem two_pow_65 : (2 : ℕ) ^ 65 = 36893488147419103232 := by norm_num

/-- The result fits in 64 unsigned bits iff `2^n * (p + 1) ≤ 2^64`. -/
theorem fits_iff (p n : ℕ) : firstKindTerm p n ≤ 2 ^ 64 - 1 ↔ 2 ^ n * (p + 1) ≤ 2 ^ 64 := by
  have h := closed_form p n
  rw [two_pow_64]
  generalize 2 ^ n * (p + 1) = b at h ⊢
  generalize firstKindTerm p n = a at h ⊢
  omega

/-- Every `n ≥ 65` overflows 64 bits, whatever `p` is. This bounds the machine loops. -/
theorem overflow_of_ge_65 (p n : ℕ) (hn : 65 ≤ n) : 2 ^ 64 - 1 < firstKindTerm p n := by
  have h := closed_form p n
  have h1 : 2 ^ 65 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 : 2 ^ n ≤ 2 ^ n * (p + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos p)
  rw [two_pow_64]
  rw [two_pow_65] at h1
  generalize 2 ^ n * (p + 1) = b at h h2
  generalize 2 ^ n = c at h1 h2
  generalize firstKindTerm p n = a at h ⊢
  omega

/-- The exact boundary: n = 64 is representable only for p = 0. -/
theorem boundary_64 :
    firstKindTerm 0 64 = 2 ^ 64 - 1 ∧ 2 ^ 64 - 1 < firstKindTerm 1 64 := by
  have a := closed_form 0 64
  have b := closed_form 1 64
  rw [two_pow_64] at a b ⊢
  omega

/-- Corpus anchor values (cf. `two_starts_firstKind_length_five`). -/
theorem anchors : (List.range 6).map (firstKindTerm 2) = [2, 5, 11, 23, 47, 95] := by
  decide

end LeanM2.Slice001

#print axioms LeanM2.Slice001.closed_form
#print axioms LeanM2.Slice001.fits_iff
#print axioms LeanM2.Slice001.overflow_of_ge_65
#print axioms LeanM2.Slice001.boundary_64
#print axioms LeanM2.Slice001.anchors
#print axioms CunninghamChain.firstKindTerm

/-! ## Reference vectors -/

namespace LeanM2.Slice001.Vectors

def u64Max : ℕ := 2 ^ 64 - 1

/-- Status codes shared with the C and Modula-2 implementations. -/
def statusOk : Int := 0
def statusOverflow : Int := 1

/-- Expected (status, value). For n ≥ 65 OVERFLOW follows from `overflow_of_ge_65`. -/
def expected (p n : ℕ) : Int × ℕ :=
  if 65 ≤ n then (statusOverflow, 0)
  else
    let v := firstKindTerm p n
    if v ≤ u64Max then (statusOk, v) else (statusOverflow, 0)

/-- 64-bit LCG (Knuth MMIX constants), for reproducible pseudo-random cases. -/
def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def seed : UInt64 := 0x5EED0001

def cases : Array (ℕ × ℕ) := Id.run do
  let ps : List ℕ := [0, 1, 2, 3, 2 ^ 32 - 1, 2 ^ 63 - 1, 2 ^ 64 - 1]
  let mut out : Array (ℕ × ℕ) := #[]
  -- grid, covering the exact boundary at n = 64 and the first certain overflow at n = 65
  for p in ps do
    for n in List.range 71 do
      out := out.push (p, n)
  -- corpus anchors
  for i in List.range 6 do
    out := out.push (2, i)
  -- large n: decided by the theorem, never computed
  for n in [100, 2 ^ 32, 2 ^ 63, 2 ^ 64 - 1] do
    out := out.push (0, n)
    out := out.push (2 ^ 64 - 1, n)
  -- pseudo-random: small p (mostly OK) and full-range p (mostly OVERFLOW)
  let mut s := seed
  for _ in List.range 1000 do
    s := lcg s
    let p := (s >>> 48).toNat
    s := lcg s
    let n := (s >>> 58).toNat            -- 0..63
    out := out.push (p, n)
  for _ in List.range 1000 do
    s := lcg s
    let p := s.toNat
    s := lcg s
    let n := ((s >>> 57).toNat) % 72     -- 0..71
    out := out.push (p, n)
  return out

def hexU64 (n : ℕ) : String := "0x" ++ String.mk (Nat.toDigits 16 n) ++ "ULL"

def cSource (cs : Array (ℕ × ℕ)) : String := Id.run do
  let mut ps := ""; let mut ns := ""; let mut sts := ""; let mut vs := ""
  for (p, n) in cs do
    let (st, v) := expected p n
    ps := ps ++ "  " ++ hexU64 p ++ ",\n"
    ns := ns ++ "  " ++ hexU64 n ++ ",\n"
    sts := sts ++ s!"  {st},\n"
    vs := vs ++ "  " ++ hexU64 v ++ ",\n"
  return "/* SPDX-License-Identifier: AGPL-3.0-only */\n/* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) */\n/* Generated by lean-m2/g3/slice001/Spec.lean from CunninghamChain.firstKindTerm\n" ++
    s!"   (formal-conjectures @ 84cf7f8, Lean {Lean.versionString}). Seed {seed}. Do not edit. */\n" ++
    "#include <stdint.h>\n#include <stddef.h>\n" ++
    s!"#define LM2_CASES {cs.size}u\n" ++
    "static const uint64_t lm2_p[LM2_CASES] = {\n" ++ ps ++ "};\n" ++
    "static const uint64_t lm2_n[LM2_CASES] = {\n" ++ ns ++ "};\n" ++
    "static const int32_t lm2_st[LM2_CASES] = {\n" ++ sts ++ "};\n" ++
    "static const uint64_t lm2_v[LM2_CASES] = {\n" ++ vs ++ "};\n" ++
    "uint32_t lm2_case_count(void) { return LM2_CASES; }\n" ++
    "int32_t lm2_case_get(uint32_t i, uint64_t *p, uint64_t *n, int32_t *st, uint64_t *v) {\n" ++
    "  if (i >= LM2_CASES || p == NULL || n == NULL || st == NULL || v == NULL) return -1;\n" ++
    "  *p = lm2_p[i]; *n = lm2_n[i]; *st = lm2_st[i]; *v = lm2_v[i];\n  return 0;\n}\n"

def jsonl (cs : Array (ℕ × ℕ)) : String :=
  cs.foldl (fun acc (p, n) =>
    let (st, v) := expected p n
    acc ++ s!"\{\"p\":\"{p}\",\"n\":\"{n}\",\"status\":{st},\"value\":\"{v}\"}\n") ""

end LeanM2.Slice001.Vectors

open LeanM2.Slice001.Vectors in
#eval show IO Unit from do
  let some out ← IO.getEnv "SLICE_OUT" | throw <| IO.userError "SLICE_OUT is not set"
  let cs := cases
  -- inputs must be representable as uint64 on the machine side
  unless cs.all (fun (p, n) => p ≤ u64Max && n ≤ u64Max) do
    throw <| IO.userError "case outside uint64 input domain"
  IO.FS.createDirAll out
  IO.FS.writeFile (System.FilePath.mk out / "lm2_cases.c") (cSource cs)
  IO.FS.writeFile (System.FilePath.mk out / "reference.jsonl") (jsonl cs)
  let okN := (cs.filter fun (p, n) => (expected p n).1 == statusOk).size
  IO.println s!"SLICE001 cases={cs.size} ok={okN} overflow={cs.size - okN} seed={seed}"
