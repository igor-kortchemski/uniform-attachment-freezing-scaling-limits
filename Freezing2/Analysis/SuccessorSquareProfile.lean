module

public import Freezing2.Analysis.SquareCorrection

/-!
# Reciprocal squares at the end of an attachment step

The printed sampled-rate assertion uses `n / S_(i+1)^2`, whereas the ordered
merger probability uses `n / (S_(i+1)(S_(i+1)-1))`. On an attachment step the
former is the reciprocal square with denominator `S_i+1` on the preceding
mesh cell. Its local L1 convergence follows from the same proved correction
estimate, without continuity or pointwise convergence assumptions.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace Freezing2

/-- Reciprocal square after adding one to the cell's active population. -/
noncomputable def successorSquareProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((n : ℝ) ^ α / ((activeCount (x n) ⌊(n : ℝ) * t⌋₊ : ℝ) + 1)) ^ 2

theorem measurable_successorSquareProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ) :
    Measurable (successorSquareProfile x α n) :=
  measurable_stepProfile (fun i ↦ ((n : ℝ) ^ α / ((activeCount (x n) i : ℝ) + 1)) ^ 2) n

theorem integrable_successorSquareProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ) :
    Integrable (successorSquareProfile x α n) profileMeasure := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold successorSquareProfile
    simp only [Nat.cast_zero, zero_mul, Nat.floor_zero, activeCount_zero, Int.cast_one]
    exact integrable_const _
  · exact integrableOn_stepProfile_Icc
      (fun i ↦ ((n : ℝ) ^ α / ((activeCount (x n) i : ℝ) + 1)) ^ 2) hn

theorem integrableOn_successorSquareProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    IntegrableOn (successorSquareProfile x α n) (Icc a b) volume := by
  have h := (integrable_successorSquareProfile x α n).restrict (s := Icc a b)
  rwa [profileMeasure_restrict_Icc ha hb] at h

/-- The successor-square error is bounded by the already controlled gap
between `S²` and `S(S+1)`. -/
theorem abs_successor_sq_sub_shifted_le {c s : ℝ} (hc : 0 ≤ c) (hs : 0 < s) :
    |(c / (s + 1)) ^ 2 - c ^ 2 / (s * (s + 1))| ≤
      |(c / s) ^ 2 - c ^ 2 / (s * (s + 1))| := by
  have hb : 0 ≤ c / (s + 1) := div_nonneg hc (by linarith)
  have hba : c / (s + 1) ≤ c / s := div_le_div_of_nonneg_left hc hs (by linarith)
  have hp : c ^ 2 / (s * (s + 1)) = (c / s) * (c / (s + 1)) := by
    rw [div_mul_div_comm]
    ring
  rw [hp]
  have hlo : (c / (s + 1)) ^ 2 ≤ (c / s) * (c / (s + 1)) := by
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hba)]
  have hhi : (c / s) * (c / (s + 1)) ≤ (c / s) ^ 2 := by
    nlinarith [mul_nonneg (hb.trans hba) (sub_nonneg.mpr hba)]
  rw [abs_of_nonpos (sub_nonpos.mpr hlo), abs_of_nonneg (sub_nonneg.mpr hhi)]
  nlinarith [sq_nonneg (c / s - c / (s + 1))]

/-- The printed squared-denominator mark has the same local L1 limit as the
exact ordered merger rate, with integrability and all finite profiles proved. -/
theorem tendsto_integral_abs_successorSquareProfile_sub_local
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : 0 < α)
    (hL1 : HasL1ReciprocalProfile x α g) (h2 : HasLocalSquareMomentProfile x α g)
    (hg0 : ∀ᵐ t ∂profileMeasure, 0 ≤ g t)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Tendsto (fun n : ℕ ↦ ∫ t in Icc a b,
      |successorSquareProfile x α n t - (g t) ^ 2|) atTop (𝓝 0) := by
  have hcorr := tendsto_integral_abs_sq_profile_sub_shifted hx hα hL1 h2 hg0 ha hab hb
  have hshift := tendsto_integral_abs_shiftedSquareProfile_sub_local hx hα hL1 h2 hg0 ha hab hb
  apply squeeze_zero (fun n ↦ integral_nonneg (fun _ ↦ abs_nonneg _)) _
    (by simpa only [add_zero] using hcorr.add hshift)
  intro n
  have hB := integrableOn_successorSquareProfile x α n ha.le hb.le
  have hP := integrableOn_shiftedSquareProfile x α n ha.le hb.le
  have hQ := integrableOn_sq_reciprocalProfile x α n ha.le hb.le
  have hG := (h2 a b ha hab hb).1
  change (∫ t in Icc a b, |successorSquareProfile x α n t - (g t) ^ 2|) ≤
    (∫ t in Icc a b, |(reciprocalProfile x α n t) ^ 2 - shiftedSquareProfile x α n t|) +
      ∫ t in Icc a b, |shiftedSquareProfile x α n t - (g t) ^ 2|
  calc
    _ ≤ ∫ t in Icc a b, |(reciprocalProfile x α n t) ^ 2 - shiftedSquareProfile x α n t| +
        |shiftedSquareProfile x α n t - (g t) ^ 2| := by
      apply integral_mono_ae (hB.sub hG).abs ((hQ.sub hP).abs.add (hP.sub hG).abs)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have hi : ⌊(n : ℝ) * t⌋₊ ≤ n := by
        apply Nat.floor_le_of_le
        simpa using mul_le_mul_of_nonneg_left (ht.2.trans hb.le) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      have hs := activeCount_real_pos hx n hi
      have hc : 0 ≤ (n : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg n) _
      have he := abs_successor_sq_sub_shifted_le hc hs
      have htri := abs_sub_le (successorSquareProfile x α n t) (shiftedSquareProfile x α n t)
        ((g t) ^ 2)
      exact htri.trans (add_le_add he le_rfl)
    _ = _ := integral_add (hQ.sub hP).abs (hP.sub hG).abs

end Freezing2
