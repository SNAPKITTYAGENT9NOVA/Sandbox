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
namespace T
/-- no instance of its own: decided through its unfolding (helpers `Small` unfolded too) -/
def SmallAndBig (n : Nat) : Prop := Small n ∧ n > 2
end T
namespace T
/-- unfolds to a statement about a noncomputable function: no Lean reference, so blocked -/
noncomputable def ncVal (n : Nat) : Nat := Classical.choice ⟨n⟩
def UsesNc (n : Nat) : Prop := ncVal n < 5
end T
namespace T
/-- no instance of its own; its unfolding is decided by Nat.decidableBallLT, which is marked
noncomputable but compiles (implemented by the compiler): must translate, not be blocked -/
def AllSmallOdd2 (n : Nat) : Prop := ∀ k < n, k % 2 = 1 → k ≠ 4
end T
namespace T
/-- ℤ results (MathIR v10): negatives, the int64 edge −2^63 (n = 2^63), and overflow -/
def zdiff (a b : Nat) : Int := (a : Int) - b
def zneg (n : Nat) : Int := -(n : Int)
def zpoly (n : Nat) : Int := 3 - (n : Int) * n
end T
namespace T
def zalt : Nat → Int
  | 0 => 1
  | n + 1 => 2 - 3 * zalt n
def zfib : Nat → Int
  | 0 => 0
  | 1 => -1
  | n + 2 => zfib (n + 1) - zfib n
end T
/-- Mathlib's `Nat.bits` (least significant bit first; [] for 0), absent from Lean core -/
def Nat.bits : Nat → List Bool
  | 0 => []
  | n + 1 => ((n + 1) % 2 == 1) :: Nat.bits ((n + 1) / 2)
decreasing_by omega
namespace T
def ones (n : Nat) : Nat := n.bits.count true
def IsThreeOnes (n : Nat) : Prop := n.bits.count true = 3
instance : DecidablePred IsThreeOnes := fun n => by unfold IsThreeOnes; infer_instance
def evensBelow (n : Nat) : List Nat := (List.range n).filter (· % 2 == 0)
def gaps (n : Nat) : Nat := (List.zip (evensBelow n) (evensBelow n).tail).countP fun pr => pr.snd - pr.fst == 2
end T
/-- Mathlib's `Nat.iterate` (absent from Lean core) -/
def Nat.iterate {α : Sort _} (op : α → α) : Nat → α → α
  | 0, a => a
  | k + 1, a => Nat.iterate op k (op a)
namespace T
def iter3 (m n : Nat) : Nat := Nat.iterate (fun x => 3 * x + 1) m n
end T
namespace T
abbrev base : Nat := 10
def lastDigit (n : Nat) : Nat := n % base
end T
namespace T
def zdivmod (a b : Nat) : Int := ((a : Int) - 100) / ((b : Int) - 7) * 1000 + ((a : Int) - 100) % ((b : Int) - 7)
end T
