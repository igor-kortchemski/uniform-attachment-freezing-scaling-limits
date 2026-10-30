module

public import Freezing2.Geometry.BirthDensity
public import Freezing2.Probability.SubcriticalProfileApproximation
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The actual limiting segment and dense profile coordinates

The image of the continuous reciprocal primitive is exactly the closed
segment in M02. Actual vertex birth coordinates become dense in this segment.
These are deterministic dependencies of geometric convergence, not a substitute
for the measured Gromov--Hausdorff--Prokhorov conclusion.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

theorem profilePrimitive_monotoneOn {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : MonotoneOn (profilePrimitive g) (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  rw [profilePrimitive_eq_setIntegral g ha.1 ha.2,
    profilePrimitive_eq_setIntegral g hb.1 hb.2]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hsub : Icc (0 : ℝ) b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hb.2
  have hgb : IntegrableOn g (Icc (0 : ℝ) b) volume :=
    (show IntegrableOn g (Icc (0 : ℝ) 1) volume from hg).mono_set hsub
  have hnb : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) b)] g :=
    ae_mono (Measure.restrict_mono hsub le_rfl) (hpos.mono fun _ h ↦ h.le)
  exact setIntegral_mono_set hgb hnb (Eventually.of_forall fun _ ht ↦
    (Icc_subset_Icc le_rfl hab) ht)

/-- The source segment is exactly the range of the primitive on the unit
interval, with its usual Euclidean distance. -/
theorem profilePrimitive_image_unitInterval {g : ℝ → ℝ}
    (hg : Integrable g profileMeasure) (hpos : PositiveProfile g) :
    profilePrimitive g '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) (profilePrimitive g 1) := by
  have h := (continuous_profilePrimitive hg).continuousOn.image_Icc_of_monotoneOn
    (by norm_num : (0 : ℝ) ≤ 1) (profilePrimitive_monotoneOn hg hpos)
  simpa only [show profilePrimitive g 0 = 0 by simp [profilePrimitive]] using h

theorem profileBirthCoordinate_mem_segment {g : ℝ → ℝ}
    (hg : Integrable g profileMeasure) (hpos : PositiveProfile g)
    (x : ℕ → ℤ) {n : ℕ} (hn : 0 < n) {v : VertexLabel}
    (hv : v ∈ vertexLabels x n) :
    profileBirthCoordinate g n v ∈ Icc (0 : ℝ) (profilePrimitive g 1) := by
  rw [← profilePrimitive_image_unitInterval hg hpos]
  refine ⟨(birthTime n v : ℝ) / n, ⟨by positivity, ?_⟩, rfl⟩
  exact (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
    (by exact_mod_cast birthTime_le x hv)

/-- No endpoint or gap in the claimed limiting segment is missed by the
actual finite vertex coordinates. -/
theorem eventually_uniform_profile_density
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ y ∈ Icc (0 : ℝ) (profilePrimitive g 1),
      ∃ v ∈ vertexLabels (x n) n, dist y (profileBirthCoordinate g n v) < ε := by
  have huc : UniformContinuousOn (profilePrimitive g) (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (continuous_profilePrimitive hL1.1).continuousOn
  obtain ⟨δ, hδ, hm⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  filter_upwards [eventually_uniform_birth_density hx hα hL1 hpos hδ,
    eventually_gt_atTop 0] with n hn hn0
  intro y hy
  rw [← profilePrimitive_image_unitInterval hL1.1 hpos] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  obtain ⟨v, hv, hclose⟩ := hn t ht
  refine ⟨v, hv, ?_⟩
  have hb : (birthTime n v : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one (by exact_mod_cast hn0 : (0 : ℝ) < n)).mpr
      (by exact_mod_cast birthTime_le (x n) hv)⟩
  exact hm t ht _ hb hclose

end Freezing2
