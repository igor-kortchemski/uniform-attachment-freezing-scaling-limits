module

public import Freezing2.Probability.DistanceApproximation
public import Freezing2.Probability.SubcriticalCoalescenceLaw
public import Freezing2.Analysis.SmallHarmonicIntervals

/-!
# Uniform segment-distance approximation in the subcritical regime

Every reverse-tree vertex is mapped to its normalized harmonic birth prefix.
The actual graph-distance error is controlled uniformly over all pairs by
N07 and the short common harmonic interval supplied by N08. The remaining
GH/GP interpretation and forward-law transport are separate obligations.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology Classical

namespace Freezing2

open ReverseHistory ReverseCoalescence

/-- Distance between the two actual deterministic prefix coordinates. -/
noncomputable def segmentDistance (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ)
    (u v : VertexLabel) : ℝ :=
  |normalizedHarmonicPrefix x α n (birthTime n u) -
    normalizedHarmonicPrefix x α n (birthTime n v)|

/-- Scaling the exact harmonic decomposition gives segment distance plus the
common interval from coalescence to minimum birth. -/
theorem normalized_coalescenceHarmonicDistance_eq
    (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ) (hs : SurvivesThrough (x n) n)
    {u v : VertexLabel} (hu : u ∈ vertexLabels (x n) n) (hv : v ∈ vertexLabels (x n) n)
    (ω : History) :
    (n : ℝ) ^ (α - 1) * coalescenceHarmonicDistance (x n) n u v ω =
      segmentDistance x α n u v + (n : ℝ) ^ (α - 1) *
        inclusiveHarmonic (x n) (sourceCoalescenceTime n u v ω)
          (min (birthTime n u) (birthTime n v)) := by
  have he := harmonic_coalescence_decomposition (x n) hs
    (sourceCoalescenceTime_le_birth_left n u v ω)
    (sourceCoalescenceTime_le_birth_right n u v ω)
    (birthTime_le (x n) hu) (birthTime_le (x n) hv)
  unfold coalescenceHarmonicDistance
  rw [he, mul_add]
  congr 1
  unfold segmentDistance normalizedHarmonicPrefix
  rw [show (n : ℝ) ^ (α - 1) * harmonicInterval (x n) 0 (birthTime n u) / 2 -
      (n : ℝ) ^ (α - 1) * harmonicInterval (x n) 0 (birthTime n v) / 2 =
      (n : ℝ) ^ (α - 1) * (harmonicInterval (x n) 0 (birthTime n u) / 2 -
        harmonicInterval (x n) 0 (birthTime n v) / 2) by ring,
    abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]

/-- The actual pairwise segment error has two explicit nonnegative controls. -/
theorem segment_distance_error_bound (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ)
    (hs : SurvivesThrough (x n) n) {u v : VertexLabel}
    (hu : u ∈ vertexLabels (x n) n) (hv : v ∈ vertexLabels (x n) n) (ω : History) :
    |(n : ℝ) ^ (α - 1) * reverseDistance n u v ω - segmentDistance x α n u v| ≤
      (n : ℝ) ^ (α - 1) * reverseDistanceErrorMax x n ω +
        (n : ℝ) ^ (α - 1) * inclusiveHarmonic (x n)
          (sourceCoalescenceTime n u v ω) (min (birthTime n u) (birthTime n v)) := by
  let C : ℝ := (n : ℝ) ^ (α - 1)
  have hC : 0 ≤ C := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hd := normalized_coalescenceHarmonicDistance_eq x α n hs hu hv ω
  have hsmall : 0 ≤ C * inclusiveHarmonic (x n) (sourceCoalescenceTime n u v ω)
      (min (birthTime n u) (birthTime n v)) := by
    apply mul_nonneg hC
    apply Finset.sum_nonneg
    intro i hi
    have hin : i ≤ n := (Finset.mem_Icc.mp hi).2.trans
      ((min_le_left _ _).trans (birthTime_le (x n) hu))
    have hS : (0 : ℝ) < activeCount (x n) i := by exact_mod_cast hs i hin
    exact inv_nonneg.mpr hS.le
  have htri := abs_sub_le (C * reverseDistance n u v ω)
    (C * coalescenceHarmonicDistance (x n) n u v ω) (segmentDistance x α n u v)
  have he : C * coalescenceHarmonicDistance (x n) n u v ω - segmentDistance x α n u v =
      C * inclusiveHarmonic (x n) (sourceCoalescenceTime n u v ω)
        (min (birthTime n u) (birthTime n v)) := by change _ at hd; linarith
  rw [he, abs_of_nonneg hsmall, ← mul_sub, abs_mul, abs_of_nonneg hC] at htri
  exact htri.trans (add_le_add
    (mul_le_mul_of_nonneg_left (distance_error_le_reverseDistanceErrorMax x n hu hv ω) hC) le_rfl)

/-- The event of some vertex pair violating the uniform segment approximation. -/
def subcriticalDistanceEvent (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ) (ε : ℝ) : Set History :=
  {ω | ∃ u ∈ vertexLabels (x n) n, ∃ v ∈ vertexLabels (x n) n,
    ε < |(n : ℝ) ^ (α - 1) * reverseDistance n u v ω - segmentDistance x α n u v|}

/-- Uniform distortion of the actual reverse tree under its harmonic-prefix
coordinate map tends to zero in probability in the subcritical regime. -/
theorem tendsto_subcriticalDistanceEvent
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (jointLaw (companionSchedule (x n)) n).real
      (subcriticalDistanceEvent x α n ε)) atTop (𝓝 0) := by
  have hα1 : α < 1 := by linarith
  obtain ⟨δ, hδ, hsmall⟩ := eventually_uniform_short_harmonic_bound hx hα1 hL1 (half_pos hε)
  have hdist := tendsto_reverseDistanceErrorMax hx hα0 hα1 hL1 hpos (half_pos hε)
  have hgap := tendsto_normalized_coalescenceGapMax_probability hx hα0 hαhalf hL1 hpos h2 hδ
  have hlim := hdist.add hgap
  simp only [zero_add] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_ hlim
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hsn hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hC : 0 ≤ (n : ℝ) ^ (α - 1) := Real.rpow_nonneg hn'.le _
  have hscale : (n : ℝ) ^ (α - 1) * (n : ℝ) ^ (1 - α) = 1 := by
    rw [← Real.rpow_add hn', show (α - 1) + (1 - α) = 0 by ring, Real.rpow_zero]
  have hincl : subcriticalDistanceEvent x α n ε ⊆
      {ω | ε / 2 * (n : ℝ) ^ (1 - α) < reverseDistanceErrorMax x n ω} ∪
      {ω | δ ≤ (coalescenceGapMax (x n) n ω : ℝ) / n} := by
    intro ω hω
    by_contra hnot
    have hdn : reverseDistanceErrorMax x n ω ≤ ε / 2 * (n : ℝ) ^ (1 - α) :=
      le_of_not_gt (fun h ↦ hnot (Or.inl h))
    have hgn : (coalescenceGapMax (x n) n ω : ℝ) / n < δ :=
      lt_of_not_ge (fun h ↦ hnot (Or.inr h))
    obtain ⟨u, hu, v, hv, herr⟩ := hω
    have hpair : coalescenceGap n u v ω ≤ coalescenceGapMax (x n) n ω := by
      unfold coalescenceGapMax
      exact Finset.le_sup (f := fun p : VertexLabel × VertexLabel ↦ coalescenceGap n p.1 p.2 ω)
        (show (u, v) ∈ (vertexLabels (x n) n).product (vertexLabels (x n) n) from
          Finset.mem_product.mpr ⟨hu, hv⟩)
    have hlen : ((min (birthTime n u) (birthTime n v) : ℕ) : ℝ) -
        sourceCoalescenceTime n u v ω ≤ δ * n := by
      rw [← coalescenceGap_cast]
      exact (show (coalescenceGap n u v ω : ℝ) ≤ coalescenceGapMax (x n) n ω by
        exact_mod_cast hpair).trans ((div_lt_iff₀ hn').mp hgn).le
    have hs := hsn (sourceCoalescenceTime n u v ω) (min (birthTime n u) (birthTime n v))
      (sourceCoalescenceTime_le_commonBirth n u v ω)
      ((min_le_left _ _).trans (birthTime_le (x n) hu)) hlen
    have hd : (n : ℝ) ^ (α - 1) * reverseDistanceErrorMax x n ω ≤ ε / 2 := by
      calc
        _ ≤ (n : ℝ) ^ (α - 1) * (ε / 2 * (n : ℝ) ^ (1 - α)) :=
          mul_le_mul_of_nonneg_left hdn hC
        _ = ε / 2 := by nlinarith [hscale]
    have hb := segment_distance_error_bound x α n (hx n).2 hu hv ω
    linarith
  exact (measureReal_mono hincl).trans (measureReal_union_le _ _)

theorem measurableSet_subcriticalDistanceEvent (x : ℕ → ℕ → ℤ) (α : ℝ)
    (n : ℕ) (ε : ℝ) : MeasurableSet (subcriticalDistanceEvent x α n ε) := by
  have he : subcriticalDistanceEvent x α n ε =
      ⋃ u ∈ vertexLabels (x n) n, ⋃ v ∈ vertexLabels (x n) n,
        {ω | ε < |(n : ℝ) ^ (α - 1) * reverseDistance n u v ω - segmentDistance x α n u v|} := by
    ext ω
    simp [subcriticalDistanceEvent]
  rw [he]
  apply MeasurableSet.biUnion (Finset.countable_toSet _)
  intro u _
  apply MeasurableSet.biUnion (Finset.countable_toSet _)
  intro v _
  have hm := (((measurable_reverseDistance n u v).const_mul ((n : ℝ) ^ (α - 1))).sub_const
    (segmentDistance x α n u v)).norm
  simpa only [Real.norm_eq_abs] using measurableSet_lt measurable_const hm

/-- Source notation and the original positive-horizon admissibility, for the
uniform distortion subclaim of the subcritical main theorem. -/
theorem tendsto_subcriticalDistanceEvent_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (jointLaw (companionSchedule (x n)) n).real
      (subcriticalDistanceEvent x α n ε)) atTop (𝓝 0) := by
  apply (tendsto_subcriticalDistanceEvent (admissible_initialRowExtension hx) hα0 hαhalf
    (hasL1ReciprocalProfile_initialRowExtension hL1) (positiveProfile_reciprocal hf)
    (hasLocalSquareMomentProfile_initialRowExtension h2) hε).congr'
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  exact congrArg (fun row : ℕ → ℤ ↦ (jointLaw (companionSchedule row) n).real
    (subcriticalDistanceEvent (fun _ ↦ row) α n ε)) hn

end Freezing2
