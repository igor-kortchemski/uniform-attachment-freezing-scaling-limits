module

public import Freezing2.Probability.SubcriticalGHLimit
public import Freezing2.Probability.BranchLengthLimit
public import Freezing2.Probability.ProkhorovBounds

/-!
# The actual vertex measure on the limiting segment

The segment carries its ordinary subtype metric and Borel structure. Its
limiting probability measure is the image of uniform time under the source
primitive. Clamping only extends this continuous map to all real times: it
changes neither uniform time nor the normalized births of actual vertices.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

/-- A continuous extension device for the source unit time interval. -/
def profileTimeClamp (t : ℝ) : ℝ := max 0 (min 1 t)

theorem profileTimeClamp_mem (t : ℝ) : profileTimeClamp t ∈ Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem profileTimeClamp_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    profileTimeClamp t = t := by
  simp only [profileTimeClamp, min_eq_right ht.2, max_eq_right ht.1]

theorem continuous_profileTimeClamp : Continuous profileTimeClamp := by
  unfold profileTimeClamp
  fun_prop

/-- The primitive as a continuous map into the actual compact segment. -/
noncomputable def profileSegmentMap (g : ℝ → ℝ) (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (t : ℝ) : ProfileSegment g :=
  ⟨profilePrimitive g (profileTimeClamp t), by
    rw [← profilePrimitive_image_unitInterval hg hpos]
    exact mem_image_of_mem _ (profileTimeClamp_mem t)⟩

theorem continuous_profileSegmentMap {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : Continuous (profileSegmentMap g hg hpos) :=
  ((continuous_profilePrimitive hg).comp continuous_profileTimeClamp).subtype_mk _

theorem profileSegmentMap_coe {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (profileSegmentMap g hg hpos t : ℝ) = profilePrimitive g t := by
  change profilePrimitive g (profileTimeClamp t) = _
  rw [profileTimeClamp_eq ht]

/-- The distinguished segment root is zero, not a sampled vertex. -/
theorem profileSegmentMap_zero {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : (profileSegmentMap g hg hpos 0 : ℝ) = 0 := by
  rw [profileSegmentMap_coe hg hpos (by constructor <;> norm_num)]
  simp [profilePrimitive]

/-- The source limiting probability measure on the true Euclidean segment. -/
noncomputable def profileSegmentMeasure (g : ℝ → ℝ) (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : ProbabilityMeasure (ProfileSegment g) :=
  profileProbabilityMeasure.map (profileSegmentMap g hg hpos)

/-- Forgetting the subtype gives exactly the primitive pushforward; there is
no modification of the limiting measure at the endpoints. -/
theorem profileSegmentMeasure_map_coe {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) :
    (profileSegmentMeasure g hg hpos).map (Subtype.val : ProfileSegment g → ℝ) =
      profileProbabilityMeasure.map (profilePrimitive g) := by
  apply Subtype.ext
  change (profileMeasure.map (profileSegmentMap g hg hpos)).map Subtype.val =
    profileMeasure.map (profilePrimitive g)
  rw [Measure.map_map measurable_subtype_coe (continuous_profileSegmentMap hg hpos).measurable]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact profileSegmentMap_coe hg hpos ht

/-- The coordinate of a paper label, extended measurably to unused labels. -/
noncomputable def profileLabelPoint (g : ℝ → ℝ) (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (n : ℕ) (v : VertexLabel) : ProfileSegment g :=
  profileSegmentMap g hg hpos ((birthTime n v : ℝ) / n)

/-- Every actual positive-horizon vertex uses its exact paper coordinate,
including frozen birth `i-1` and active birth `n`. -/
theorem profileLabelPoint_coe {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (x : ℕ → ℤ) {n : ℕ} (hn : 0 < n)
    {v : VertexLabel} (hv : v ∈ vertexLabels x n) :
    (profileLabelPoint g hg hpos n v : ℝ) = profileBirthCoordinate g n v := by
  apply profileSegmentMap_coe hg hpos
  refine ⟨by positivity, ?_⟩
  exact (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
    (by exact_mod_cast birthTime_le x hv)

/-- The genuine uniform vertex measure transported to profile coordinates. -/
noncomputable def uniformProfileCoordinateLaw (x : ℕ → ℤ) (n : ℕ) (hx : IsSigned x)
    (hs : 0 ≤ activeCount x n) (g : ℝ → ℝ) (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : ProbabilityMeasure (ProfileSegment g) :=
  (uniformLabelProbability x n hx hs).map (profileLabelPoint g hg hpos n)

theorem uniformProfileCoordinateLaw_eq_birth_map (x : ℕ → ℤ) (n : ℕ)
    (hx : IsSigned x) (hs : 0 ≤ activeCount x n) {g : ℝ → ℝ}
    (hg : Integrable g profileMeasure) (hpos : PositiveProfile g) :
    uniformProfileCoordinateLaw x n hx hs g hg hpos =
      (uniformBirthProbability x n hx hs).map (profileSegmentMap g hg hpos) := by
  apply Subtype.ext
  change (uniformVertex x n).map (profileLabelPoint g hg hpos n) =
    ((uniformVertex x n).map (fun v ↦ (birthTime n v : ℝ) / n)).map
      (profileSegmentMap g hg hpos)
  rw [Measure.map_map (continuous_profileSegmentMap hg hpos).measurable
    (measurable_of_countable _)]
  rfl

/-- On actual support this is the unclamped paper coordinate law. -/
theorem uniformProfileCoordinateLaw_map_coe (x : ℕ → ℤ) {n : ℕ} (hn : 0 < n)
    (hx : IsSigned x) (hs : 0 ≤ activeCount x n) {g : ℝ → ℝ}
    (hg : Integrable g profileMeasure) (hpos : PositiveProfile g) :
    ((uniformProfileCoordinateLaw x n hx hs g hg hpos : Measure (ProfileSegment g)).map
      (Subtype.val : ProfileSegment g → ℝ)) =
      (uniformVertex x n).map (profileBirthCoordinate g n) := by
  change ((uniformVertex x n).map (profileLabelPoint g hg hpos n)).map Subtype.val = _
  rw [Measure.map_map measurable_subtype_coe (measurable_of_countable _)]
  apply Measure.map_congr
  filter_upwards [uniformVertex_mem x hx hs] with v hv
  exact profileLabelPoint_coe hg hpos x hn hv

/-- Weak convergence of the actual coordinate measure, on the segment itself. -/
theorem tendsto_uniformProfileCoordinateLaw {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n ↦ uniformProfileCoordinateLaw (x n) n (hx n).1
      ((hx n).2 n le_rfl).le g hL1.1 hpos) atTop
      (𝓝 (profileSegmentMeasure g hL1.1 hpos)) := by
  simp only [uniformProfileCoordinateLaw_eq_birth_map, profileSegmentMeasure]
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_uniformBirthProbability hx hα hL1 hpos)
    (continuous_profileSegmentMap hL1.1 hpos)

/-- The measure part of M02 uses the genuine Lévy--Prokhorov distance for
probability measures on the Euclidean subtype segment. -/
theorem tendsto_profileCoordinate_levyProkhorovDist
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n ↦ levyProkhorovDist
      (uniformProfileCoordinateLaw (x n) n (hx n).1 ((hx n).2 n le_rfl).le
        g hL1.1 hpos : Measure (ProfileSegment g))
      (profileSegmentMeasure g hL1.1 hpos : Measure (ProfileSegment g))) atTop (𝓝 0) :=
  tendsto_levyProkhorovDist_of_tendsto (tendsto_uniformProfileCoordinateLaw hx hα hL1 hpos)

/-- For the paper profile `f`, the limiting measure is precisely uniform time
pushed through its displayed integral of `1/(2*f)`. -/
theorem profileSegmentMeasure_reciprocal_map_coe {f : ℝ → ℝ}
    (hg : Integrable (fun t ↦ 1 / f t) profileMeasure)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t) :
    (profileSegmentMeasure (fun t ↦ 1 / f t) hg (positiveProfile_reciprocal hf)).map
      (Subtype.val : ProfileSegment (fun t ↦ 1 / f t) → ℝ) =
      profileProbabilityMeasure.map (sourceBranchPrimitive f) := by
  rw [profileSegmentMeasure_map_coe, profilePrimitive_reciprocal_map_eq]

/-- The source has assumptions only at positive horizons. Replacing the unused
zero row and taking the sequence `n+1` preserves the exact measured limit. -/
theorem tendsto_profileCoordinate_levyProkhorovDist_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα : α < 1) (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t)) :
    Tendsto (fun n ↦ levyProkhorovDist
      (uniformProfileCoordinateLaw (x (n + 1)) (n + 1)
        (hx (n + 1) (Nat.zero_lt_succ n)).1
        ((hx (n + 1) (Nat.zero_lt_succ n)).2 (n + 1) le_rfl).le
        (fun t ↦ 1 / f t) hL1.1 (positiveProfile_reciprocal hf) :
          Measure (ProfileSegment (fun t ↦ 1 / f t)))
      (profileSegmentMeasure (fun t ↦ 1 / f t) hL1.1 (positiveProfile_reciprocal hf) :
        Measure (ProfileSegment (fun t ↦ 1 / f t)))) atTop (𝓝 0) := by
  have h := (tendsto_profileCoordinate_levyProkhorovDist
    (admissible_initialRowExtension hx) hα
    (hasL1ReciprocalProfile_initialRowExtension hL1) (positiveProfile_reciprocal hf)).comp
      (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, initialRowExtension, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, ↓reduceIte] using h

end Freezing2
