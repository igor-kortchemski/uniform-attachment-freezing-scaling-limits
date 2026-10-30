module

public import Freezing2.Geometry.GromovHausdorffProkhorov
public import Freezing2.Probability.ProfileForestMeasure

/-!
# Measured subcritical approximation in the source GHP distance

The actual finite tree carries its uniform vertex measure. Its profile map
has small distortion, dense image, and the proved Prokhorov limit. A single
common metric realization gives the source's summed GHP-distance bound.
Forward-law transport and the quotient-space distribution interface are separate.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

open ReverseHistory

/-- GHP distance from the scaled finite forest with its actual uniform vertex
measure to the measured source segment. The zero fallback only totalizes the
function outside the positive-scale connected domain. -/
noncomputable def forestGHPDistance (g : ℝ → ℝ) (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (c : ℝ) (F : Freezing1.Reverse.Forest) : ℝ :=
  if h : F.toGraph.Connected ∧ 0 < c then
    letI := scaledGraphMetric F.toGraph h.1 c h.2
    ghpDistance (forestVertexMeasure F) (profileSegmentMeasure g hg hpos : Measure (ProfileSegment g))
  else 0

noncomputable def reverseGHPDistance (g : ℝ → ℝ) (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (α : ℝ) (n : ℕ) (ω : History) : ℝ :=
  forestGHPDistance g hg hpos ((n : ℝ) ^ (α - 1)) (forestAt n 0 ω)

theorem measurable_reverseGHPDistance (g : ℝ → ℝ) (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (α : ℝ) (n : ℕ) :
    Measurable (reverseGHPDistance g hg hpos α n) := by
  have hm : Measurable (forestGHPDistance g hg hpos ((n : ℝ) ^ (α - 1))) := measurable_from_top
  change Measurable (fun ω : History ↦ forestGHPDistance g hg hpos ((n : ℝ) ^ (α - 1)) (ω n))
  exact hm.comp (measurable_pi_apply n)

theorem reverseGHPDistance_le {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hg : Integrable g profileMeasure) (hpos : PositiveProfile g)
    {n : ℕ} (hn : 0 < n) (ω : History)
    (hF : Freezing1.Reverse.ValidAt (companionSchedule (x n)) n 0 (forestAt n 0 ω))
    {δ r p : ℝ} (hδ : 0 < δ)
    (hdense : ∀ y ∈ Icc (0 : ℝ) (profilePrimitive g 1),
      ∃ v ∈ vertexLabels (x n) n, dist y (profileBirthCoordinate g n v) ≤ r)
    (herror : ∀ u ∈ vertexLabels (x n) n, ∀ v ∈ vertexLabels (x n) n,
      |(n : ℝ) ^ (α - 1) * reverseDistance n u v ω -
        (|profileBirthCoordinate g n u - profileBirthCoordinate g n v|)| ≤ 2 * δ)
    (hprob : levyProkhorovDist
      (uniformProfileCoordinateLaw (x n) n (hx n).1 ((hx n).2 n le_rfl).le
        g hg hpos : Measure (ProfileSegment g))
      (profileSegmentMeasure g hg hpos : Measure (ProfileSegment g)) ≤ p) :
    reverseGHPDistance g hg hpos α n ω ≤ 2 * δ + r + p := by
  let F := forestAt n 0 ω
  have hV : F.vertices = Freezing1.vertexLabels (companionSchedule (x n)) n := by
    simpa only [Freezing1.Reverse.phaseLabels_zero] using hF.vertices_eq
  have hroot : F.roots.card = 1 := by simpa using hF.roots_card
  have hconn : F.toGraph.Connected := (F.isTree_of_one_root hroot hF.acyclic).1
  have hc : 0 < (n : ℝ) ^ (α - 1) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  let := scaledGraphMetric F.toGraph hconn ((n : ℝ) ^ (α - 1)) hc
  let := hconn.nonempty
  let := profileSegment_nonempty hg hpos
  have hnon : F.vertices.Nonempty := by
    obtain ⟨v⟩ := hconn.nonempty
    exact ⟨v.val, v.property⟩
  let := forestVertexMeasure_isProbabilityMeasure F hnon
  let f := forestProfilePoint g hg hpos n F
  have hlabel (v : {v // v ∈ F.vertices}) : fromCompanionLabel v.val ∈ vertexLabels (x n) n :=
    (fromCompanionLabel_mem_iff (x n) (hx n).1 n v.val).mpr (hV ▸ v.property)
  have hcoe (v : {v // v ∈ F.vertices}) : (f v : ℝ) =
      profileBirthCoordinate g n (fromCompanionLabel v.val) :=
    forestProfilePoint_coe hg hpos (hx n).1 hn hV v
  have hd : ∀ y : ProfileSegment g, ∃ v, dist y (f v) ≤ r := by
    intro y
    obtain ⟨v, hv, hyv⟩ := hdense y.val y.property
    have hmem : toCompanionLabel v ∈ F.vertices := hV ▸ toCompanionLabel_mem (x n) (hx n).1 hv
    refine ⟨⟨toCompanionLabel v, hmem⟩, ?_⟩
    rw [Subtype.dist_eq, hcoe, from_toCompanionLabel hv]
    exact hyv
  have he : ∀ u v : {v // v ∈ F.vertices}, |dist u v - dist (f u) (f v)| ≤ 2 * δ := by
    intro u v
    change |(n : ℝ) ^ (α - 1) * (F.toGraph.dist u v : ℝ) - dist (f u) (f v)| ≤ 2 * δ
    rw [forest_toGraph_dist_eq F u v, Subtype.dist_eq, hcoe u, hcoe v, Real.dist_eq]
    simpa only [reverseDistance, to_fromCompanionLabel] using herror _ (hlabel u) _ (hlabel v)
  have hp : levyProkhorovDist ((forestVertexMeasure F).map f)
      (profileSegmentMeasure g hg hpos : Measure (ProfileSegment g)) ≤ p := by
    rw [map_forestVertexMeasure_profilePoint_of_valid (hx n).1 ((hx n).2 n le_rfl).le hF hg hpos]
    exact hprob
  have hb := ghpDistance_le_of_approx (forestVertexMeasure F)
    (profileSegmentMeasure g hg hpos : Measure (ProfileSegment g)) f
    (measurable_forestProfilePoint hg hpos n F) hδ he hd hp
  change forestGHPDistance g hg hpos ((n : ℝ) ^ (α - 1)) F ≤ _
  simpa only [forestGHPDistance,
    dite_eq_left (show F.toGraph.Connected ∧ 0 < (n : ℝ) ^ (α - 1) from ⟨hconn, hc⟩)] using hb

/-- Actual uniform measured reverse trees converge in probability for the
manuscript's ambient-isometry GHP infimum, with its summed cost convention. -/
theorem tendsto_reverseGHPDistance_probability
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (jointLaw (companionSchedule (x n)) n).real
      {ω | ε < reverseGHPDistance g hL1.1 hpos α n ω}) atTop (𝓝 0) := by
  have hα1 : α < 1 := by linarith
  have hd := tendsto_subcriticalProfileEvent hx hα0 hαhalf hL1 hpos h2
    (show 0 < ε / 4 by positivity)
  have hr := eventually_uniform_profile_density hx hα1 hL1 hpos (show 0 < ε / 4 by positivity)
  have hp := (tendsto_profileCoordinate_levyProkhorovDist hx hα1 hL1 hpos).eventually_lt_const
    (show 0 < ε / 4 by positivity)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_ hd
  filter_upwards [hr, hp, eventually_gt_atTop 0] with n hrn hpn hn
  have hsub : {ω | ε < reverseGHPDistance g hL1.1 hpos α n ω}
      ≤ᵐ[jointLaw (companionSchedule (x n)) n] subcriticalProfileEvent x α g n (ε / 4) := by
    filter_upwards [jointLaw_forestAt_valid (companionSchedule (x n)) n
      (companion_before_extinction (x n) (hx n).1 (hx n).2).le] with ω hvalid
    intro hbad
    by_contra he
    have hbound := reverseGHPDistance_le (α := α) hx hL1.1 hpos hn ω (hvalid 0 (Nat.zero_le n))
      (show 0 < ε / 8 by positivity)
      (fun y hy ↦ by obtain ⟨v, hv, hclose⟩ := hrn y hy; exact ⟨v, hv, hclose.le⟩)
      (by
        intro u hu v hv
        have h : |(n : ℝ) ^ (α - 1) * reverseDistance n u v ω -
            (|profileBirthCoordinate g n u - profileBirthCoordinate g n v|)| ≤ ε / 4 :=
          le_of_not_gt (fun h ↦ he ⟨u, hu, v, hv, h⟩)
        linarith) hpn.le
    change ε < reverseGHPDistance g hL1.1 hpos α n ω at hbad
    linarith
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)

/-- Original positive-horizon assumptions and source reciprocal profile, with
the exact limiting image measure supplied by `profileSegmentMeasure`. -/
theorem tendsto_reverseGHPDistance_probability_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (jointLaw (companionSchedule (x n)) n).real
      {ω | ε < reverseGHPDistance (fun t ↦ 1 / f t) hL1.1 (positiveProfile_reciprocal hf) α n ω})
      atTop (𝓝 0) := by
  apply (tendsto_reverseGHPDistance_probability (admissible_initialRowExtension hx)
    hα0 hαhalf (hasL1ReciprocalProfile_initialRowExtension hL1) (positiveProfile_reciprocal hf)
    (hasLocalSquareMomentProfile_initialRowExtension h2) hε).congr'
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  exact congrArg (fun row : ℕ → ℤ ↦ (jointLaw (companionSchedule row) n).real
    {ω | ε < reverseGHPDistance (fun t ↦ 1 / f t) hL1.1 (positiveProfile_reciprocal hf) α n ω}) hn

end Freezing2
