module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-!
# Deterministic attachment and freezing schedules

The paper indexes its signs by the positive integers. Here a schedule has domain
`ℕ`, but its value at zero is ignored: `true` at `i + 1` means attachment at
step `i + 1`, and `false` means freezing. The integer walk is not truncated at
zero; `PositiveThrough x n` expresses that extinction has not occurred by `n`.
-/

@[expose] public section

namespace Freezing1

/-- An attachment/freezing schedule; index zero is unused. -/
abbrev SignSequence := ℕ → Bool

/-- Number of attachment steps among steps `1, …, n`. -/
def plusCount (x : SignSequence) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if x (i + 1) then 1 else 0

/-- Number of freezing steps among steps `1, …, n`. -/
def minusCount (x : SignSequence) (n : ℕ) : ℕ := n - plusCount x n

/-- The integer walk `S_n = 1 + ∑_{i=1}^n x_i` from the Introduction. -/
def activeCount (x : SignSequence) (n : ℕ) : ℤ :=
  1 + ∑ i ∈ Finset.range n, if x (i + 1) then 1 else -1

/-- Positivity of the walk up to and including time `n`, i.e. `τ > n`. -/
def PositiveThrough (x : SignSequence) (n : ℕ) : Prop :=
  ∀ k ≤ n, 0 < activeCount x k

@[simp] theorem plusCount_zero (x : SignSequence) : plusCount x 0 = 0 := by
  simp [plusCount]

@[simp] theorem plusCount_succ (x : SignSequence) (n : ℕ) :
    plusCount x (n + 1) = plusCount x n + if x (n + 1) then 1 else 0 := by
  simp only [plusCount, Finset.sum_range_succ]

@[simp] theorem activeCount_zero (x : SignSequence) : activeCount x 0 = 1 := by
  simp [activeCount]

theorem activeCount_succ (x : SignSequence) (n : ℕ) :
    activeCount x (n + 1) = activeCount x n + if x (n + 1) then 1 else -1 := by
  simp [activeCount, Finset.sum_range_succ, add_assoc]

theorem plusCount_le (x : SignSequence) (n : ℕ) : plusCount x n ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [plusCount_succ]
    split <;> omega

/-- The counting identity used throughout the paper. -/
theorem activeCount_eq (x : SignSequence) (n : ℕ) :
    activeCount x n = 1 + 2 * (plusCount x n : ℤ) - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [activeCount_succ, plusCount_succ, ih]
    cases x (n + 1) <;> simp <;> omega

theorem plusCount_add_minusCount (x : SignSequence) (n : ℕ) :
    plusCount x n + minusCount x n = n := by
  simp [minusCount, Nat.add_sub_of_le (plusCount_le x n)]

theorem activeCount_eq_counts (x : SignSequence) (n : ℕ) :
    activeCount x n = 1 + (plusCount x n : ℤ) - minusCount x n := by
  rw [activeCount_eq, minusCount, Nat.cast_sub (plusCount_le x n)]
  ring

theorem activeCount_le_plusCount_add_one (x : SignSequence) (n : ℕ) :
    activeCount x n ≤ (plusCount x n : ℤ) + 1 := by
  rw [activeCount_eq_counts]
  omega

theorem PositiveThrough.mono {x : SignSequence} {m n : ℕ}
    (h : PositiveThrough x n) (hmn : m ≤ n) : PositiveThrough x m :=
  fun k hk => h k (hk.trans hmn)

/-- Before extinction, attachment steps comprise at least half of all steps. -/
theorem le_two_mul_plusCount {x : SignSequence} {n : ℕ}
    (h : PositiveThrough x n) : n ≤ 2 * plusCount x n := by
  have hn := h n le_rfl
  rw [activeCount_eq] at hn
  omega

end Freezing1
