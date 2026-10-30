module

public import Freezing2.Geometry.ProfileSegment
public import Freezing2.Geometry.ForestGH

/-!
# Actual subcritical Gromov--Hausdorff convergence

Uniform distortion and density give convergence in probability of the actual
scaled reverse-tree isometry class to the source segment. This establishes
the GH part only: the measured GHP conclusion and forward-law transport remain
separate obligations.
-/

@[expose] public section

open Filter MeasureTheory Set GromovHausdorff
open scoped Topology Classical

namespace Freezing2

open ReverseHistory

abbrev ProfileSegment (g : ℝ → ℝ) := {y : ℝ // y ∈ Icc (0 : ℝ) (profilePrimitive g 1)}

theorem profileSegment_nonempty {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : Nonempty (ProfileSegment g) := by
  have h := profilePrimitive_monotoneOn hg hpos
    (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) (by norm_num)
  have h0 : 0 ≤ profilePrimitive g 1 := by
    simpa only [show profilePrimitive g 0 = 0 by simp [profilePrimitive]] using h
  exact ⟨⟨0, le_rfl, h0⟩⟩

/-- The exact source segment with its Euclidean metric, represented in GHSpace. -/
noncomputable def profileSegmentGH (g : ℝ → ℝ) (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : GHSpace := by
  letI := profileSegment_nonempty hg hpos
  exact toGHSpace (ProfileSegment g)

/-- Distance in the genuine GH metric. The actual reverse forest is connected
almost surely, so the totalization in `forestScaledGHSpace` has no effect. -/
noncomputable def reverseGHDistance (g : ℝ → ℝ) (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (α : ℝ) (n : ℕ) (ω : History) : ℝ :=
  dist (forestScaledGHSpace (forestAt n 0 ω) ((n : ℝ) ^ (α - 1)))
    (profileSegmentGH g hg hpos)

theorem measurable_reverseGHDistance (g : ℝ → ℝ) (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (α : ℝ) (n : ℕ) :
    Measurable (reverseGHDistance g hg hpos α n) := by
  have hm : Measurable (fun F : Freezing1.Reverse.Forest ↦
      dist (forestScaledGHSpace F ((n : ℝ) ^ (α - 1))) (profileSegmentGH g hg hpos)) :=
    measurable_from_top
  change Measurable (fun ω : History ↦
    dist (forestScaledGHSpace (ω n) ((n : ℝ) ^ (α - 1))) (profileSegmentGH g hg hpos))
  exact hm.comp (measurable_pi_apply n)

/-- On every valid actual terminal forest the deterministic density and
distortion estimates bound its true GH distance to the entire segment. -/
theorem reverseGHDistance_le {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hg : Integrable g profileMeasure) (hpos : PositiveProfile g)
    {n : ℕ} (hn : 0 < n) (ω : History)
    (hF : Freezing1.Reverse.ValidAt (companionSchedule (x n)) n 0 (forestAt n 0 ω))
    {D r : ℝ}
    (hdense : ∀ y ∈ Icc (0 : ℝ) (profilePrimitive g 1),
      ∃ v ∈ vertexLabels (x n) n, dist y (profileBirthCoordinate g n v) ≤ r)
    (herror : ∀ u ∈ vertexLabels (x n) n, ∀ v ∈ vertexLabels (x n) n,
      |(n : ℝ) ^ (α - 1) * reverseDistance n u v ω -
        (|profileBirthCoordinate g n u - profileBirthCoordinate g n v|)| ≤ D) :
    reverseGHDistance g hg hpos α n ω ≤ D / 2 + r := by
  let F := forestAt n 0 ω
  have hV : F.vertices = Freezing1.vertexLabels (companionSchedule (x n)) n := by
    simpa only [Freezing1.Reverse.phaseLabels_zero] using hF.vertices_eq
  have hroot : F.roots.card = 1 := by simpa using hF.roots_card
  have hconn : F.toGraph.Connected := (F.isTree_of_one_root hroot hF.acyclic).1
  have hc : 0 < (n : ℝ) ^ (α - 1) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  let := profileSegment_nonempty hg hpos
  have hlabel (v : {v // v ∈ F.vertices}) : fromCompanionLabel v.val ∈ vertexLabels (x n) n :=
    (fromCompanionLabel_mem_iff (x n) (hx n).1 n v.val).mpr (hV ▸ v.property)
  let f : {v // v ∈ F.vertices} → ProfileSegment g := fun v ↦
    ⟨profileBirthCoordinate g n (fromCompanionLabel v.val),
      profileBirthCoordinate_mem_segment hg hpos (x n) hn (hlabel v)⟩
  have hd : ∀ y : ProfileSegment g, ∃ v, dist y (f v) ≤ r := by
    intro y
    obtain ⟨v, hv, hyv⟩ := hdense y.val y.property
    have hmem : toCompanionLabel v ∈ F.vertices := hV ▸ toCompanionLabel_mem (x n) (hx n).1 hv
    refine ⟨⟨toCompanionLabel v, hmem⟩, ?_⟩
    simpa only [f, Subtype.dist_eq, from_toCompanionLabel hv] using hyv
  have he : ∀ u v, |(n : ℝ) ^ (α - 1) * (F.toGraph.dist u v : ℝ) - dist (f u) (f v)| ≤ D := by
    intro u v
    rw [forest_toGraph_dist_eq F u v]
    have h := herror _ (hlabel u) _ (hlabel v)
    simpa only [reverseDistance, to_fromCompanionLabel,
      f, F, Subtype.dist_eq, Real.dist_eq] using h
  exact forestScaledGHSpace_dist_le F _ hconn hc f hd he

/-- The GH part of M02, under the actual reverse-tree history law. -/
theorem tendsto_reverseGHDistance_probability
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (jointLaw (companionSchedule (x n)) n).real
      {ω | ε < reverseGHDistance g hL1.1 hpos α n ω}) atTop (𝓝 0) := by
  have hd := tendsto_subcriticalProfileEvent hx hα0 hαhalf hL1 hpos h2 hε
  have hr := eventually_uniform_profile_density hx (show α < 1 by linarith) hL1 hpos
    (show 0 < ε / 4 by positivity)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_ hd
  filter_upwards [hr, eventually_gt_atTop 0] with n hrn hn
  have hsub : {ω | ε < reverseGHDistance g hL1.1 hpos α n ω} ≤ᵐ[jointLaw (companionSchedule (x n)) n]
      subcriticalProfileEvent x α g n ε := by
    filter_upwards [jointLaw_forestAt_valid (companionSchedule (x n)) n
      (companion_before_extinction (x n) (hx n).1 (hx n).2).le] with ω hvalid
    intro hbad
    by_contra he
    have hp : ∀ u ∈ vertexLabels (x n) n, ∀ v ∈ vertexLabels (x n) n,
        |(n : ℝ) ^ (α - 1) * reverseDistance n u v ω -
          (|profileBirthCoordinate g n u - profileBirthCoordinate g n v|)| ≤ ε := by
      intro u hu v hv
      exact le_of_not_gt (fun h ↦ he ⟨u, hu, v, hv, h⟩)
    have hbound := reverseGHDistance_le hx hL1.1 hpos hn ω (hvalid 0 (Nat.zero_le n))
      (fun y hy ↦ by obtain ⟨v, hv, hclose⟩ := hrn y hy; exact ⟨v, hv, hclose.le⟩) hp
    change ε < reverseGHDistance g hL1.1 hpos α n ω at hbad
    linarith
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)

/-- Original source profile and admissibility only at positive horizons.
The target is the exact segment with endpoint `∫₀¹ 1/(2f)` by the proved
primitive identity. Its measure and the GHP conclusion remain separate. -/
theorem tendsto_reverseGHDistance_probability_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα0 : 0 < α) (hαhalf : α < 1 / 2)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (jointLaw (companionSchedule (x n)) n).real
      {ω | ε < reverseGHDistance (fun t ↦ 1 / f t) hL1.1 (positiveProfile_reciprocal hf) α n ω})
      atTop (𝓝 0) := by
  apply (tendsto_reverseGHDistance_probability (admissible_initialRowExtension hx)
    hα0 hαhalf (hasL1ReciprocalProfile_initialRowExtension hL1) (positiveProfile_reciprocal hf)
    (hasLocalSquareMomentProfile_initialRowExtension h2) hε).congr'
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  exact congrArg (fun row : ℕ → ℤ ↦ (jointLaw (companionSchedule row) n).real
    {ω | ε < reverseGHDistance (fun t ↦ 1 / f t) hL1.1 (positiveProfile_reciprocal hf) α n ω}) hn

end Freezing2
