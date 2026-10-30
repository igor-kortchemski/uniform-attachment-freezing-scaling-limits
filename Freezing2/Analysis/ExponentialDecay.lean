module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.Ring

/-!
# Polynomial factors versus stretched exponential decay

These analytic estimates discharge the final numerical decay step in polynomial
union bounds, as used at source lines 910–915 and 940–950.  They do not supply
the preceding stochastic bounds or their positive constants.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Freezing2

/-- Every real power is dominated by `exp (-c * x^a)` when `a,c > 0`. -/
theorem tendsto_rpow_mul_exp_neg_rpow (k : ℝ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ k * Real.exp (-c * x ^ a)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k / a) c hc).comp
    (tendsto_rpow_atTop ha)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  dsimp
  rw [← Real.rpow_mul hx, mul_div_cancel₀ k ha.ne']

/-- Natural-indexed version, including arbitrary real polynomial exponents. -/
theorem tendsto_nat_rpow_mul_exp_neg_rpow (k : ℝ) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-c * (n : ℝ) ^ a)) atTop (𝓝 0) :=
  (tendsto_rpow_mul_exp_neg_rpow k ha hc).comp tendsto_natCast_atTop_atTop

/-- Integer polynomial degrees can use the ordinary power notation. -/
theorem tendsto_nat_pow_mul_exp_neg_rpow (k : ℕ) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-c * (n : ℝ) ^ a)) atTop (𝓝 0) := by
  simpa only [Real.rpow_natCast] using tendsto_nat_rpow_mul_exp_neg_rpow (k : ℝ) ha hc

/-- The `2 n²` union-bound prefactor in the distance comparison causes no obstruction to decay. -/
theorem tendsto_two_nat_sq_mul_exp_neg_rpow {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun n : ℕ => 2 * (n : ℝ) ^ 2 * Real.exp (-c * (n : ℝ) ^ a)) atTop (𝓝 0) := by
  simpa only [mul_assoc, mul_zero] using
    (tendsto_nat_pow_mul_exp_neg_rpow 2 ha hc).const_mul 2

/-- The `(n+1)²` prefactor for all pairs of vertices also tends to zero. -/
theorem tendsto_nat_succ_sq_mul_exp_neg_rpow {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * Real.exp (-c * (n : ℝ) ^ a))
      atTop (𝓝 0) := by
  have h₂ := tendsto_nat_pow_mul_exp_neg_rpow 2 ha hc
  have h₁ := (tendsto_nat_pow_mul_exp_neg_rpow 1 ha hc).const_mul 2
  have h₀ := tendsto_nat_pow_mul_exp_neg_rpow 0 ha hc
  have h := (h₂.add h₁).add h₀
  simp only [add_zero, mul_zero] at h
  apply h.congr
  intro n
  ring

/-- The exponent in the subcritical coalescence estimate is positive precisely below `1/2`. -/
theorem tendsto_subcritical_pair_bound {α c : ℝ} (hα : α < 1 / 2) (hc : 0 < c) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 *
      Real.exp (-c * (n : ℝ) ^ (1 - 2 * α))) atTop (𝓝 0) := by
  apply tendsto_nat_succ_sq_mul_exp_neg_rpow (by linarith) hc

/-- Polynomial union bounds also vanish with the floor exponent in the bounded-height regime.
This includes `q = 0`, when the power is eventually identically zero. -/
theorem tendsto_nat_succ_sq_mul_geometric_floor {q ε : ℝ} (hq₀ : 0 ≤ q)
    (hq₁ : q < 1) (hε : 0 < ε) (M : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 *
      q ^ ((⌊ε * (n : ℝ)⌋₊ : ℝ) / 2 - M)) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le hq₀ with hq | hq
  · subst q
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_gt_atTop ((2 * M + 1) / ε))] with n hn
    have hn' : 2 * M + 1 < ε * (n : ℝ) := by
      have h := (div_lt_iff₀ hε).mp hn
      nlinarith
    have hf := Nat.lt_floor_add_one (ε * (n : ℝ))
    have he : 0 < (⌊ε * (n : ℝ)⌋₊ : ℝ) / 2 - M := by linarith
    simp [Real.zero_rpow he.ne']
  · let c : ℝ := -(Real.log q) * ε / 2
    have hc : 0 < c := div_pos (mul_pos (neg_pos.mpr (Real.log_neg hq hq₁)) hε)
      (by norm_num)
    have hlim := (tendsto_nat_succ_sq_mul_exp_neg_rpow (a := 1) (by norm_num) hc).const_mul
      (Real.exp (-Real.log q * (M + 1 / 2)))
    simp only [Real.rpow_one, mul_zero] at hlim
    apply squeeze_zero (fun n => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hq.le _))
      (fun n => ?_) hlim
    have hf := Nat.lt_floor_add_one (ε * (n : ℝ))
    have hp : q ^ ((⌊ε * (n : ℝ)⌋₊ : ℝ) / 2 - M) ≤
        q ^ (ε * (n : ℝ) / 2 - M - 1 / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hq hq₁.le (by linarith)
    calc
      ((n : ℝ) + 1) ^ 2 * q ^ ((⌊ε * (n : ℝ)⌋₊ : ℝ) / 2 - M)
          ≤ ((n : ℝ) + 1) ^ 2 * q ^ (ε * (n : ℝ) / 2 - M - 1 / 2) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = Real.exp (-Real.log q * (M + 1 / 2)) *
          (((n : ℝ) + 1) ^ 2 * Real.exp (-c * (n : ℝ))) := by
        rw [Real.rpow_def_of_pos hq]
        have he : Real.log q * (ε * (n : ℝ) / 2 - M - 1 / 2) =
            -Real.log q * (M + 1 / 2) + -c * (n : ℝ) := by dsimp [c]; ring
        rw [he, Real.exp_add]
        ring

end Freezing2
