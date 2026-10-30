module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# An absorbing-safe coalescent count recurrence

The source bounds expected cluster counts by telescoping reciprocals of their
excess above one. The case where that excess is zero is treated first; no
reciprocal of a vanishing excess is used. These deterministic estimates will
be applied only after the actual stochastic recurrence has been proved.
-/

@[expose] public section

open scoped BigOperators

namespace Freezing2

/-- One positive quadratic decrement increases the reciprocal by at least
its rate divided by the population-square bound. -/
theorem reciprocal_increment_of_quadratic_decrement
    {w v a B : ℝ} (hv : 0 < v) (ha : 0 ≤ a) (hB : 0 < B)
    (hstep : v ≤ w - a * w ^ 2 / B) :
    a / B ≤ 1 / v - 1 / w := by
  have hvw : v ≤ w := hstep.trans (sub_le_self _ (by positivity))
  have hw : 0 < w := hv.trans_le hvw
  have hloss : a * w ^ 2 ≤ B * (w - v) := by
    have h := (div_le_iff₀ hB).mp (show a * w ^ 2 / B ≤ w - v by linarith)
    nlinarith
  have hinv : 1 / v - 1 / w = (w - v) / (v * w) := by
    field_simp
  rw [hinv]
  apply (div_le_div_iff₀ hB (mul_pos hv hw)).mpr
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hvw hw.le) ha
  nlinarith

/-- A nonnegative sequence with quadratic loss is bounded by the inverse
accumulated rate. The zero absorbing case is included explicitly. -/
theorem quadratic_decrement_bound
    (w a : ℕ → ℝ) {n : ℕ} {B : ℝ} (hB : 0 < B)
    (hw : ∀ j ≤ n, 0 ≤ w j) (ha : ∀ j < n, 0 ≤ a j)
    (hstep : ∀ j < n, w (j + 1) ≤ w j - a j * (w j) ^ 2 / B)
    (hsum : 0 < ∑ j ∈ Finset.range n, a j) :
    w n ≤ B / (∑ j ∈ Finset.range n, a j) := by
  by_cases hz : w n = 0
  · rw [hz]
    exact div_nonneg hB.le hsum.le
  have hn : 0 < w n := lt_of_le_of_ne (hw n le_rfl) (Ne.symm hz)
  have hdec (j : ℕ) (hj : j < n) : w (j + 1) ≤ w j :=
    (hstep j hj).trans (sub_le_self _ (div_nonneg
      (mul_nonneg (ha j hj) (sq_nonneg _)) hB.le))
  have hmono : AntitoneOn w (Set.Iic n) := by
    apply antitoneOn_of_succ_le Set.ordConnected_Iic
    intro j _ _ hj
    exact hdec j (Nat.lt_of_succ_le hj)
  have hpos (j : ℕ) (hj : j ≤ n) : 0 < w j :=
    hn.trans_le (hmono hj (show n ≤ n from le_rfl) hj)
  have hrec : (∑ j ∈ Finset.range n, a j) / B ≤ 1 / w n - 1 / w 0 := by
    have h := Finset.sum_le_sum (fun j (hj : j ∈ Finset.range n) ↦
      reciprocal_increment_of_quadratic_decrement
        (hpos (j + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))
        (ha j (Finset.mem_range.mp hj)) hB (hstep j (Finset.mem_range.mp hj)))
    simpa only [← Finset.sum_div, Finset.sum_range_sub (fun j ↦ 1 / w j) n] using h
  have hrec' : (∑ j ∈ Finset.range n, a j) / B ≤ 1 / w n :=
    hrec.trans (sub_le_self _ (one_div_nonneg.mpr (hpos 0 (Nat.zero_le n)).le))
  have hprod := (div_le_div_iff₀ hB hn).mp hrec'
  apply (le_div_iff₀ hsum).mpr
  nlinarith

/-- The source expected-count form. This is a deterministic consequence of
the displayed recurrence, not an assumption that the tree process obeys it. -/
theorem expected_cluster_count_bound_of_recurrence
    (u a : ℕ → ℝ) {n : ℕ} {B : ℝ} (hB : 0 < B)
    (hu : ∀ j ≤ n, 1 ≤ u j) (ha : ∀ j < n, 0 ≤ a j)
    (hstep : ∀ j < n, u (j + 1) ≤ u j - a j * u j * (u j - 1) / B)
    (hsum : 0 < ∑ j ∈ Finset.range n, a j) :
    u n ≤ 1 + B / (∑ j ∈ Finset.range n, a j) := by
  have h := quadratic_decrement_bound (fun j ↦ u j - 1) a hB
    (fun j hj ↦ sub_nonneg.mpr (hu j hj)) ha (fun j hj ↦ ?_) hsum
  · linarith
  · have hp : 0 ≤ a j * (u j - 1) := mul_nonneg (ha j hj)
      (sub_nonneg.mpr (hu j (Nat.le_of_lt hj)))
    have hnum : a j * (u j - 1) ^ 2 ≤ a j * u j * (u j - 1) := by nlinarith
    have hd := div_le_div_of_nonneg_right hnum hB.le
    have hs := hstep j hj
    linarith

end Freezing2
