module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Uniform geometric tail bounds for dyadic chaining

The constant is selected before the initial index and the number of terms.
This supplies the numerical tail bound in U31; the stochastic block estimates
and ordered probability limits remain separate.
-/

@[expose] public section

open Filter
open scoped Topology BigOperators

namespace Freezing2

/-- A polynomial times a geometric sequence has a tail bounded by any
strictly slower geometric sequence, with one constant for every tail. -/
theorem exists_polynomial_geometric_tail_bound (p : ℕ) {q r : ℝ}
    (hq : 0 ≤ q) (hqr : q < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ k m : ℕ,
      (∑ j ∈ Finset.range m, ((k + j : ℕ) : ℝ) ^ p * q ^ (k + j)) ≤ C * r ^ k := by
  have hr : 0 < r := hq.trans_lt hqr
  have hlim := tendsto_pow_const_mul_const_pow_of_lt_one p
    (div_nonneg hq hr.le) ((div_lt_one hr).mpr hqr)
  obtain ⟨B, hB⟩ := hlim.bddAbove_range
  let D : ℝ := max B 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hterm (i : ℕ) : (i : ℝ) ^ p * q ^ i ≤ D * r ^ i := by
    have hb : (i : ℝ) ^ p * (q / r) ^ i ≤ D :=
      (hB (Set.mem_range_self i)).trans (le_max_left _ _)
    have h := mul_le_mul_of_nonneg_right hb (pow_nonneg hr.le i)
    simpa only [div_pow, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hr.ne')] using h
  refine ⟨D * (1 - r)⁻¹, mul_pos hD (inv_pos.mpr (sub_pos.mpr hr1)), ?_⟩
  intro k m
  calc
    _ ≤ ∑ j ∈ Finset.range m, D * r ^ (k + j) :=
      Finset.sum_le_sum (fun j _ ↦ hterm (k + j))
    _ = D * r ^ k * ∑ j ∈ Finset.range m, r ^ j := by
      simp only [pow_add, ← mul_assoc, Finset.mul_sum]
    _ ≤ D * r ^ k * (1 - r)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD.le (pow_nonneg hr.le _))
      simpa only [tsum_geometric_of_lt_one hr.le hr1] using
        (summable_geometric_of_lt_one hr.le hr1).sum_le_tsum
          (Finset.range m) (fun j _ ↦ pow_nonneg hr.le j)
    _ = _ := by ring

/-- The exact real-power bound used in the paper's dyadic chaining argument. -/
theorem exists_dyadic_chaining_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ k m : ℕ,
      (∑ j ∈ Finset.range m,
        ((k + j : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (-((k + j : ℕ) : ℝ) / 2)) ≤
      C * (2 : ℝ) ^ (-(k : ℝ) / 3) := by
  have hq : 0 ≤ (2 : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hqr : (2 : ℝ) ^ (-(1 : ℝ) / 2) < (2 : ℝ) ^ (-(1 : ℝ) / 3) := by
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have hr1 : (2 : ℝ) ^ (-(1 : ℝ) / 3) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  obtain ⟨C, hC, hb⟩ := exists_polynomial_geometric_tail_bound 2 hq hqr hr1
  refine ⟨C, hC, ?_⟩
  intro k m
  have he (i : ℕ) (a : ℝ) : ((2 : ℝ) ^ (-1 / a)) ^ i = (2 : ℝ) ^ (-(i : ℝ) / a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  simpa only [he] using hb k m

end Freezing2
