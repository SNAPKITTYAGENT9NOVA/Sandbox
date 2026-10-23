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
namespace T
def zcall (n : Nat) : Int := if n % 2 = 0 then zfib (n + 1) / 2 else -(zalt (n - 1))
end T
namespace T
/-- strong recursion (well-founded on n): calls at n / 2 and n - 2 -/
def stern (n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else if n % 2 = 0 then stern (n / 2)
  else stern (n / 2) + stern (n / 2 + 1)
termination_by n
decreasing_by all_goals omega
end T
/-- Mathlib's `Nat.strongRec` (absent from Lean core) -/
def Nat.strongRec {motive : Nat → Sort _} (ind : ∀ n, (∀ m, m < n → motive m) → motive n) : ∀ n, motive n
  | n => ind n fun m _ => Nat.strongRec ind m
decreasing_by assumption
namespace T
def conv2 (b : Nat → Nat) (n : Nat) : Nat := (List.range (n + 1)).foldl (fun acc k => acc + b k * b (n - k)) 0
/-- Catalan numbers through Nat.strongRec and a higher-order helper -/
def catalan : Nat → Nat :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else
      let b : Nat → Nat := fun m => if h : m < n then ih m h else 0
      conv2 b (n - 1)
end T
namespace T
/-- eta-expanded form of the same definition -/
def catalan' (n : Nat) : Nat :=
  Nat.strongRec (fun n ih =>
    if n = 0 then 1
    else
      let b : Nat → Nat := fun m => if h : m < n then ih m h else 0
      conv2 b (n - 1)) n
end T
namespace T
/-- binary strong recursion (ℤ), the shape of OeisA112521.T -/
def T2 (n k : Nat) : Int :=
  if n = 0 ∨ k = 0 then 0
  else if n = 1 ∧ k = 1 then 1
  else T2 n (k - 2) + T2 n (k - 1) - 2 * T2 (n - 1) (k - 1) + T2 (n - 1) k + T2 (n - 2) k
termination_by n + k
decreasing_by all_goals omega
/-- binary strong recursion (ℕ): binomial coefficients by Pascal's rule -/
def pascal (n k : Nat) : Nat :=
  if k = 0 then 1 else if n = 0 then 0 else pascal (n - 1) (k - 1) + pascal (n - 1) k
termination_by n
decreasing_by all_goals omega
end T
namespace T
/-- diagonal recursion (Erdős 835's johnsonBound, verbatim) -/
def johnsonBound : Nat → Nat → Nat → Nat
  | 0, _d, _w => 1
  | _n, _d, 0 => 1
  | n + 1, d, w + 1 => if 2 * (w + 1) < d then 1 else (n + 1) * johnsonBound n d w / (w + 1)
/-- diagonal recursion with argument-dependent bases -/
def diagSum : Nat → Nat → Nat
  | 0, w => w + 7
  | n, 0 => 2 * n
  | n + 1, w + 1 => diagSum n w + n * w + 1
end T
