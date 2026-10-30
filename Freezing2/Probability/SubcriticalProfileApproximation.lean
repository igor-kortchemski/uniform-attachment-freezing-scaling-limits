module

public import Freezing2.Probability.SubcriticalDistanceApproximation

/-!
# Uniform distortion under the fixed limiting profile coordinates

The harmonic coordinates are replaced by the limiting primitive evaluated at
the actual normalized reverse birth times. The replacement error is uniform,
so the result concerns every vertex pair of the actual reverse tree.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology Classical

namespace Freezing2

open ReverseHistory

noncomputable def profileBirthCoordinate (g : ℝ → ℝ) (n : ℕ) (v : VertexLabel) : ℝ :=
  profilePrimitive g ((birthTime n v : ℝ) / n)

theorem segmentDistance_profile_error_le {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hg : Integrable g profileMeasure) {n : ℕ} (hn : 0 < n)
    {u v : VertexLabel} (hu : u ∈ vertexLabels (x n) n) (hv : v ∈ vertexLabels (x n) n) :
    |segmentDistance x α n u v -
      (|profileBirthCoordinate g n u - profileBirthCoordinate g n v|)| ≤
        2 * branchPrimitiveError x α g n := by
  have hu' := normalizedHarmonicPrefix_error_le (α := α) hx hg hn (birthTime_le (x n) hu)
  have hv' := normalizedHarmonicPrefix_error_le (α := α) hx hg hn (birthTime_le (x n) hv)
  have ht := abs_abs_sub_abs_le_abs_sub
    (normalizedHarmonicPrefix x α n (birthTime n u) - normalizedHarmonicPrefix x α n (birthTime n v))
    (profileBirthCoordinate g n u - profileBirthCoordinate g n v)
  have he : normalizedHarmonicPrefix x α n (birthTime n u) -
      normalizedHarmonicPrefix x α n (birthTime n v) -
      (profileBirthCoordinate g n u - profileBirthCoordinate g n v) =
      (normalizedHarmonicPrefix x α n (birthTime n u) - profileBirthCoordinate g n u) -
      (normalizedHarmonicPrefix x α n (birthTime n v) - profileBirthCoordinate g n v) := by ring
  rw [he] at ht
  have htri := abs_sub
    (normalizedHarmonicPrefix x α n (birthTime n u) - profileBirthCoordinate g n u)
    (normalizedHarmonicPrefix x α n (birthTime n v) - profileBirthCoordinate g n v)
  change |segmentDistance x α n u v - _| ≤ _ at ht
  change |_ - profileBirthCoordinate g n u| ≤ _ at hu'
  change |_ - profileBirthCoordinate g n v| ≤ _ at hv'
  linarith

def subcriticalProfileEvent (x : ℕ → ℕ → ℤ) (α : ℝ) (g : ℝ → ℝ) (n : ℕ) (ε : ℝ) :
    Set History :=
  {ω | ∃ u ∈ vertexLabels (x n) n, ∃ v ∈ vertexLabels (x n) n,
    ε < |(n : ℝ) ^ (α - 1) * reverseDistance n u v ω -
      (|profileBirthCoordinate g n u - profileBirthCoordinate g n v|)|}

/-- Uniform convergence in probability of graph distances to distances between
the fixed continuous profile coordinates, with the full source assumptions. -/
theorem tendsto_subcriticalProfileEvent
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (jointLaw (companionSchedule (x n)) n).real
      (subcriticalProfileEvent x α g n ε)) atTop (𝓝 0) := by
  have hd := tendsto_subcriticalDistanceEvent hx hα0 hαhalf hL1 hpos h2 (half_pos hε)
  have he := (tendsto_branchPrimitiveError (show α < 1 by linarith) hL1).eventually_lt_const
    (show 0 < ε / 4 by positivity)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_ hd
  filter_upwards [he, eventually_gt_atTop 0] with n hen hn
  apply measureReal_mono (s₂ := subcriticalDistanceEvent x α n (ε / 2)) _ (measure_ne_top _ _)
  intro ω hω
  obtain ⟨u, hu, v, hv, hbad⟩ := hω
  refine ⟨u, hu, v, hv, ?_⟩
  have hb := segmentDistance_profile_error_le (α := α) hx hL1.1 hn hu hv
  have ht := abs_sub_le ((n : ℝ) ^ (α - 1) * reverseDistance n u v ω)
    (segmentDistance x α n u v)
    |profileBirthCoordinate g n u - profileBirthCoordinate g n v|
  linarith

theorem measurableSet_subcriticalProfileEvent (x : ℕ → ℕ → ℤ) (α : ℝ)
    (g : ℝ → ℝ) (n : ℕ) (ε : ℝ) : MeasurableSet (subcriticalProfileEvent x α g n ε) := by
  have he : subcriticalProfileEvent x α g n ε =
      ⋃ u ∈ vertexLabels (x n) n, ⋃ v ∈ vertexLabels (x n) n,
        {ω | ε < |(n : ℝ) ^ (α - 1) * reverseDistance n u v ω -
          (|profileBirthCoordinate g n u - profileBirthCoordinate g n v|)|} := by
    ext ω
    simp [subcriticalProfileEvent]
  rw [he]
  apply MeasurableSet.biUnion (Finset.countable_toSet _)
  intro u _
  apply MeasurableSet.biUnion (Finset.countable_toSet _)
  intro v _
  have hm := (((measurable_reverseDistance n u v).const_mul ((n : ℝ) ^ (α - 1))).sub_const
    |profileBirthCoordinate g n u - profileBirthCoordinate g n v|).norm
  simpa only [Real.norm_eq_abs] using measurableSet_lt measurable_const hm

end Freezing2
