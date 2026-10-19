-- SPDX-License-Identifier: AGPL-3.0-only
-- Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project)
-- MathIR end-to-end fixture (Lean core only), run by build.sh: each definition is either
-- translated and checked against Lean, or blocked for the stated reason (report.golden).
namespace T
def sq (n : Nat) : Nat := n * n
/-- bounded ∀ -/
def AllSmallOdd (n : Nat) : Prop := ∀ k < n, k % 2 = 1 → k ≠ 4
instance : DecidablePred AllSmallOdd := fun n => by unfold AllSmallOdd; infer_instance
/-- bounded ∃ with ≤ -/
def HasSqBelow (n m : Nat) : Prop := ∃ k ≤ n, k * k = m
instance (n m : Nat) : Decidable (HasSqBelow n m) := by unfold HasSqBelow; infer_instance
/-- membership in a list source, ↔, implication -/
def InRange (n m : Nat) : Prop := (m ∈ List.range n) ↔ (m < n)
instance (n m : Nat) : Decidable (InRange n m) := by unfold InRange; infer_instance
/-- helper predicate inlined -/
def Small (n : Nat) : Prop := n < 10
def SmallAndEven (n : Nat) : Prop := Small n ∧ n % 2 = 0
instance : DecidablePred SmallAndEven := fun n => by unfold SmallAndEven Small; infer_instance
/-- Bool with List.any -/
def anyDiv (n : Nat) : Bool := (List.range n).any (fun d => d > 1 && n % d == 0)
/-- predicate with no Decidable instance: must be blocked (no reference) -/
def Unbounded (n : Nat) : Prop := ∀ k, k + n ≥ n
noncomputable instance : DecidablePred Unbounded := fun n => Classical.propDecidable _
def NoInst (n : Nat) : Prop := ∃ k, k > n
end T
