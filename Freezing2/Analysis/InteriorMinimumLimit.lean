module

public import Freezing2.Analysis.InteriorMinimum
public import Freezing2.Analysis.PopulationMinimum

/-!
# Growth of the interior population minimum

Equation `eq:cvminSinfini` follows by applying the shrinking-window estimate
to the actual minimizing times. For `α ≥ 1/2`, it also gives the divergence
of the interior minimum asserted after the source's profile hypotheses.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Freezing2

/-- Equation `eq:cvminSinfini` for the genuine minimum on `[a n,b n]`. -/
theorem tendsto_scaled_reciprocal_interiorMinimum
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (2 * α - 1) /
      (activeCount (x n) (interiorMinimizer x n a b) : ℝ)) atTop (𝓝 0) :=
  tendsto_rpow_reciprocal_population_of_sublinear hx hL1 h2
    (fun n ↦ interiorMinimizer x n a b) (fun n ↦ interiorMinimizer_le x n a b)
    ha hab.le hb (eventually_interiorMinimizer_window x ha.le hab hb.le)
    (interiorMinimizer_population_sublinear hx hα hL1 hpos ha.le hab hb.le)

/-- The interior minimum diverges in the critical and supercritical regimes. -/
theorem tendsto_interiorMinimum_atTop
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 1 / 2 ≤ α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Tendsto (fun n : ℕ ↦ (activeCount (x n) (interiorMinimizer x n a b) : ℝ))
      atTop atTop := by
  have hscaled := tendsto_scaled_reciprocal_interiorMinimum hx hα1 hL1 hpos h2 ha hab hb
  have hinv : Tendsto (fun n : ℕ ↦
      (activeCount (x n) (interiorMinimizer x n a b) : ℝ)⁻¹) atTop (𝓝 0) := by
    have hnonneg (n : ℕ) : 0 ≤ (activeCount (x n) (interiorMinimizer x n a b) : ℝ)⁻¹ :=
      inv_nonneg.mpr (activeCount_real_pos hx n (interiorMinimizer_le x n a b)).le
    apply squeeze_zero' (Eventually.of_forall hnonneg) ?_ hscaled
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp := Real.one_le_rpow hn1 (show 0 ≤ 2 * α - 1 by linarith)
    simpa only [one_div] using div_le_div_of_nonneg_right hp
      (activeCount_real_pos hx n (interiorMinimizer_le x n a b)).le
  have hinvpos : ∀ᶠ n : ℕ in atTop,
      (activeCount (x n) (interiorMinimizer x n a b) : ℝ)⁻¹ ∈ Set.Ioi 0 :=
    Eventually.of_forall fun n ↦ inv_pos.mpr
      (activeCount_real_pos hx n (interiorMinimizer_le x n a b))
  have hwithin := tendsto_nhdsWithin_iff.mpr ⟨hinv, hinvpos⟩
  simpa only [Function.comp_def, inv_inv] using tendsto_inv_nhdsGT_zero.comp hwithin

end Freezing2
