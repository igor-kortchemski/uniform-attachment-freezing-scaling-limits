module

public import Freezing2.Discrete.Estimates
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Reciprocal population profiles

The definitions use the original integer walk and the source's right-continuous
mesh convention `S_(floor(nt))`. Positivity of the limiting reciprocal profile
is stated almost everywhere, so endpoint zeros of the original profile are
permitted and Lean's total inverse cannot silently admit a positive-measure
zero set. The finite spike estimate is the skip-free step behind `hnalpha(i)`.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Freezing2

/-- A triangular array with signed increments and survival throughout each horizon. -/
def AdmissibleArray (x : ℕ → ℕ → ℤ) : Prop :=
  ∀ n, IsSigned (x n) ∧ SurvivesThrough (x n) n

/-- Lebesgue measure on the source's unit time interval. -/
noncomputable abbrev profileMeasure : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- The scaled reciprocal population in the source's `Lim` hypotheses. -/
noncomputable def reciprocalProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) ^ α / (activeCount (x n) ⌊(n : ℝ) * t⌋₊ : ℝ)

/-- The source's `L¹` convergence, expressed without choosing representatives in `Lp`.
Integrability of the mesh profiles is a consequence of their finite range. -/
def HasL1ReciprocalProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (g : ℝ → ℝ) : Prop :=
  Integrable g profileMeasure ∧
    Tendsto (fun n ↦ ∫ t, |reciprocalProfile x α n t - g t| ∂profileMeasure)
      atTop (𝓝 0)

/-- The reciprocal of the source's finite positive profile is positive a.e.
Endpoint values do not affect this hypothesis. -/
def PositiveProfile (g : ℝ → ℝ) : Prop := ∀ᵐ t ∂profileMeasure, 0 < g t

/-- One unit change per time step bounds every forward increment of the walk. -/
theorem activeCount_real_sub_le (x : ℕ → ℤ) (hx : IsSigned x) {a b : ℕ}
    (hab : a ≤ b) :
    (activeCount x b : ℝ) - activeCount x a ≤ (b : ℝ) - a := by
  have hs := upSteps_card_add_downSteps_card x hx (a := a) (b := b)
  have hd := upSteps_card_sub_downSteps_card x hx hab
  have hi : activeCount x b - activeCount x a ≤ (b : ℤ) - a := by omega
  exact_mod_cast hi

/-- A population spike controls a whole preceding real-time interval, with the
single rounding error displayed explicitly. -/
theorem activeCount_floor_lower (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ)
    {a t : ℝ} (ht : 0 ≤ t) (hta : t ≤ a) :
    (activeCount x ⌊(n : ℝ) * a⌋₊ : ℝ) - (n : ℝ) * (a - t) - 1 ≤
      activeCount x ⌊(n : ℝ) * t⌋₊ := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hab : ⌊(n : ℝ) * t⌋₊ ≤ ⌊(n : ℝ) * a⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hta hn)
  have hs := activeCount_real_sub_le x hx hab
  have hfa := Nat.floor_le (mul_nonneg hn (ht.trans hta))
  have hft := Nat.lt_floor_add_one ((n : ℝ) * t)
  nlinarith

/-- Quantitative spike estimate used in the proof of `hnalpha(i)`.
The cutoff and interval are fixed independently of `n`. -/
theorem reciprocalProfile_le_of_spike (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ)
    (hx : IsSigned (x n)) {a t δ ε : ℝ}
    (hε : 0 < ε) (hn : 4 ≤ ε * (n : ℝ))
    (ht : 0 ≤ t) (hta : t ≤ a) (hat : a - δ ≤ t) (hδ : δ ≤ ε / 4)
    (hspike : ε * (n : ℝ) ≤ activeCount (x n) ⌊(n : ℝ) * a⌋₊) :
    reciprocalProfile x α n t ≤ (2 / ε) * ((n : ℝ) ^ α / (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by nlinarith
  have hlow := activeCount_floor_lower (x n) hx n ht hta
  have hmul : (n : ℝ) * (a - t) ≤ (n : ℝ) * (ε / 4) :=
    mul_le_mul_of_nonneg_left (by linarith) hnpos.le
  have hden : ε * (n : ℝ) / 2 ≤ (activeCount (x n) ⌊(n : ℝ) * t⌋₊ : ℝ) := by
    linarith
  have hpos : 0 < ε * (n : ℝ) / 2 := by positivity
  unfold reciprocalProfile
  calc
    _ ≤ (n : ℝ) ^ α / (ε * (n : ℝ) / 2) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hnpos.le _) hpos hden
    _ = _ := by field_simp

/-- The upper bound forced by a spike tends to zero for every sublinear exponent. -/
theorem tendsto_profile_spike_bound {α ε : ℝ} (hα : α < 1) (_hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ (2 / ε) * ((n : ℝ) ^ α / (n : ℝ))) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (α - 1)) atTop (𝓝 0) :=
    by simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have he : (fun n : ℕ ↦ (n : ℝ) ^ α / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (α - 1)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [Real.rpow_sub (by exact_mod_cast hn : (0 : ℝ) < n), Real.rpow_one]
  simpa using (hpow.congr' he.symm).const_mul (2 / ε)

end Freezing2
