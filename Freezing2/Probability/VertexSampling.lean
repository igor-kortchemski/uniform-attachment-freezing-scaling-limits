module

public import Freezing2.Probability.BirthTimeLimit
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Repeated uniform samples and active labels

The exact collision probability is retained when using coalescence statements
that require distinct vertices. This addresses the sampling gap in source issue
S07; it does not assume that independent samples are always different.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal Classical

namespace Freezing2

/-- A uniform sample belongs to the actual finite label set almost surely. -/
theorem uniformVertex_mem (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) : ∀ᵐ v ∂uniformVertex x n, v ∈ vertexLabels x n := by
  let := uniformVertex_isProbabilityMeasure x hx hs
  apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
  rw [uniformVertex, Measure.uniformOfFinset_apply]
  simp only [mem_ofPred_eq, Finset.filter_mem_eq_inter, Finset.inter_self]
  exact ENNReal.div_self (by exact_mod_cast (vertexLabels_nonempty x hx hs).card_pos.ne')
    (by simp)

/-- Two independently sampled vertices coincide with probability exactly the
reciprocal vertex count, including the one-vertex case. -/
theorem uniformVertex_collision (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) :
    ((uniformVertex x n).prod (uniformVertex x n)).real {p | p.1 = p.2} =
      1 / (vertexLabels x n).card := by
  let := uniformVertex_isProbabilityMeasure x hx hs
  unfold Measure.real
  rw [Measure.prod_apply ((Set.to_countable _).measurableSet)]
  have he : (fun v : VertexLabel ↦ (uniformVertex x n) {w | v = w}) =ᵐ[uniformVertex x n]
      (fun _ ↦ ((vertexLabels x n).card : ℝ≥0∞)⁻¹) := by
    filter_upwards [uniformVertex_mem x hx hs] with v hv
    have hsng : {w : VertexLabel | v = w} = {v} := by ext w; simp [eq_comm]
    rw [hsng]
    exact Measure.uniformOfFinset_apply_singleton_of_mem hv
  have hpre : (fun v : VertexLabel ↦ (uniformVertex x n) (Prod.mk v ⁻¹' {p | p.1 = p.2})) =
      (fun v ↦ (uniformVertex x n) {w | v = w}) := rfl
  rw [hpre, lintegral_congr_ae he]
  simp

/-- The collision correction tends to zero under the source profile hypothesis. -/
theorem tendsto_uniformVertex_collision {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n ↦ ((uniformVertex (x n) n).prod (uniformVertex (x n) n)).real
      {p | p.1 = p.2}) atTop (𝓝 0) := by
  have hnum : Tendsto (fun n : ℕ ↦ 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim := hnum.div (tendsto_normalized_vertexLabels_card hx hα hL1 hpos)
    (by norm_num : (1 : ℝ) ≠ 0)
  simp only [zero_div] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [uniformVertex_collision (x n) (hx n).1 ((hx n).2 n le_rfl).le]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change (2 / (n : ℝ)) / ((2 / (n : ℝ)) * (vertexLabels (x n) n).card) = _
  simpa only [mul_one] using mul_div_mul_left (1 : ℝ)
    ((vertexLabels (x n) n).card : ℝ) (div_ne_zero (by norm_num) hn')

end Freezing2
