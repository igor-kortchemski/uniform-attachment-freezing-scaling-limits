module

public import Freezing2.Analysis.SublinearPopulation
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Macroscopic counts of the two signs

These are the interval-count asymptotics in equation `eq:pn`, used by
Lemma `lem:hnalpha(ii)`. They include the endpoint `a=0`, where the initial
population is exactly one, and retain both floor-rounding terms explicitly.
Weak convergence of the associated finite measures is a separate conclusion.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Freezing2

/-- Normalized mesh times converge to their real-time parameter. -/
theorem tendsto_floor_time_div {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ ↦ (⌊(n : ℝ) * a⌋₊ : ℝ) / n) atTop (𝓝 a) := by
  simpa only [Function.comp_def, mul_comm] using
    (tendsto_nat_floor_mul_div_atTop ha).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Sublinearity including the initial endpoint, whose population is one. -/
theorem population_sublinear_at_nonneg {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Tendsto (fun n : ℕ ↦ (activeCount (x n) ⌊(n : ℝ) * a⌋₊ : ℝ) / n)
      atTop (𝓝 0) := by
  rcases eq_or_lt_of_le ha0 with ha | ha
  · subst a
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  · exact population_sublinear_at hx hα hL1 hpos ha ha1

/-- Twice the number of attachment times in a fixed macroscopic interval,
divided by the horizon, converges to that interval's length. -/
theorem tendsto_upSteps_macroscopic {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun n : ℕ ↦ (2 / (n : ℝ)) *
      (upSteps (x n) ⌊(n : ℝ) * a⌋₊ ⌊(n : ℝ) * b⌋₊).card)
      atTop (𝓝 (b - a)) := by
  have hSa := population_sublinear_at_nonneg hx hα hL1 hpos ha (hab.trans hb)
  have hSb := population_sublinear_at_nonneg hx hα hL1 hpos (ha.trans hab) hb
  have hl := (((tendsto_floor_time_div (ha.trans hab)).sub
    (tendsto_floor_time_div ha)).add hSb).sub hSa
  simp only [add_zero, sub_zero] at hl
  apply hl.congr
  intro n
  have hfloor : ⌊(n : ℝ) * a⌋₊ ≤ ⌊(n : ℝ) * b⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg n))
  have hc : (2 : ℝ) *
      (upSteps (x n) ⌊(n : ℝ) * a⌋₊ ⌊(n : ℝ) * b⌋₊).card =
      (⌊(n : ℝ) * b⌋₊ : ℝ) - (⌊(n : ℝ) * a⌋₊ : ℝ) +
      (activeCount (x n) ⌊(n : ℝ) * b⌋₊ : ℝ) -
      (activeCount (x n) ⌊(n : ℝ) * a⌋₊ : ℝ) := by
    exact_mod_cast twice_upSteps_card (x n) (hx n).1 hfloor
  calc
    _ = ((⌊(n : ℝ) * b⌋₊ : ℝ) - (⌊(n : ℝ) * a⌋₊ : ℝ) +
      (activeCount (x n) ⌊(n : ℝ) * b⌋₊ : ℝ) -
      (activeCount (x n) ⌊(n : ℝ) * a⌋₊ : ℝ)) / n := by ring
    _ = _ := by rw [← hc]; ring

/-- The same macroscopic interval limit holds for freezing times. -/
theorem tendsto_downSteps_macroscopic {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun n : ℕ ↦ (2 / (n : ℝ)) *
      (downSteps (x n) ⌊(n : ℝ) * a⌋₊ ⌊(n : ℝ) * b⌋₊).card)
      atTop (𝓝 (b - a)) := by
  have hSa := population_sublinear_at_nonneg hx hα hL1 hpos ha (hab.trans hb)
  have hSb := population_sublinear_at_nonneg hx hα hL1 hpos (ha.trans hab) hb
  have hl := (((tendsto_floor_time_div (ha.trans hab)).sub
    (tendsto_floor_time_div ha)).sub hSb).add hSa
  simp only [add_zero, sub_zero] at hl
  apply hl.congr
  intro n
  have hfloor : ⌊(n : ℝ) * a⌋₊ ≤ ⌊(n : ℝ) * b⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg n))
  have hc : (2 : ℝ) *
      (downSteps (x n) ⌊(n : ℝ) * a⌋₊ ⌊(n : ℝ) * b⌋₊).card =
      (⌊(n : ℝ) * b⌋₊ : ℝ) - (⌊(n : ℝ) * a⌋₊ : ℝ) -
      (activeCount (x n) ⌊(n : ℝ) * b⌋₊ : ℝ) +
      (activeCount (x n) ⌊(n : ℝ) * a⌋₊ : ℝ) := by
    exact_mod_cast twice_downSteps_card (x n) (hx n).1 hfloor
  calc
    _ = ((⌊(n : ℝ) * b⌋₊ : ℝ) - (⌊(n : ℝ) * a⌋₊ : ℝ) -
      (activeCount (x n) ⌊(n : ℝ) * b⌋₊ : ℝ) +
      (activeCount (x n) ⌊(n : ℝ) * a⌋₊ : ℝ)) / n := by ring
    _ = _ := by rw [← hc]; ring

end Freezing2
