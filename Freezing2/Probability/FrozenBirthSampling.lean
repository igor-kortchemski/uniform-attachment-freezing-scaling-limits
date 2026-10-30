module

public import Freezing2.Probability.AuxiliarySignSampling

/-!
# Frozen-label samples and the auxiliary birth-time law

The frozen label `inl (i + 1)` has source birth time `i`. This finite bijection
identifies iid frozen labels with the manuscript's auxiliary freezing times,
and identifies distinct frozen-label conditioning with distinct auxiliary birth
conditioning. No collision or active-label contribution is silently removed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Classical

namespace Freezing2

/-- An injection on a finite support transports its distinct vectors exactly. -/
theorem image_distinctSampleVectors {A B : Type*} [DecidableEq B] (s : Finset A) (f : A → B)
    (hf : Set.InjOn f (s : Set A)) (k : ℕ) :
    (distinctSampleVectors s k).image (fun v i ↦ f (v i)) =
      distinctSampleVectors (s.image f) k := by
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rcases mem_distinctSampleVectors.mp hv with ⟨hmem, hinj⟩
    apply mem_distinctSampleVectors.mpr
    exact ⟨fun i ↦ Finset.mem_image.mpr ⟨v i, hmem i, rfl⟩,
      fun i j he ↦ hinj (hf (hmem i) (hmem j) he)⟩
  · intro hw
    rcases mem_distinctSampleVectors.mp hw with ⟨hmem, hinj⟩
    have hex : ∀ i, ∃ a ∈ s, f a = w i := fun i ↦ Finset.mem_image.mp (hmem i)
    choose v hv he using hex
    apply Finset.mem_image.mpr
    refine ⟨v, mem_distinctSampleVectors.mpr ⟨hv, ?_⟩, funext he⟩
    intro i j hij
    apply hinj
    rw [← he i, ← he j, hij]

/-- Distinct frozen labels have distinct source birth times. -/
theorem birthTime_injOn_frozenVertexLabels (x : ℕ → ℤ) (n : ℕ) :
    Set.InjOn (birthTime n) (frozenVertexLabels x n : Set VertexLabel) := by
  intro u hu v hv he
  rw [frozenVertexLabels_eq] at hu hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hu
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hv
  have hi0 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hi).1).1
  have hj0 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hj).1).1
  change i - 1 = j - 1 at he
  have hij : i = j := by omega
  rw [hij]

theorem frozenVertexLabels_image_birthTime (x : ℕ → ℤ) (n : ℕ) :
    (frozenVertexLabels x n).image (birthTime n) = auxiliarySignTimes x (-1) n := by
  rw [frozenVertexLabels_eq, Finset.map_eq_image, Finset.image_image]
  simpa only [Function.comp_def, Function.Embedding.inl_apply, birthTime,
    auxiliarySignSteps, downSteps, zero_add] using auxiliarySignSteps_image_pred x (-1) n

/-- Exact one-coordinate law before normalization of time. -/
theorem map_uniformFrozen_birthTime (x : ℕ → ℤ) (n : ℕ) :
    (Measure.uniformOfFinset (frozenVertexLabels x n)).map (birthTime n) =
      Measure.uniformOfFinset (auxiliarySignTimes x (-1) n) := by
  rw [map_uniformOfFinset_of_injOn _ _ (measurable_of_countable _)
    (birthTime_injOn_frozenVertexLabels x n), frozenVertexLabels_image_birthTime]

/-- The iid frozen-label vector has exactly the iid auxiliary birth-index law. -/
theorem map_iidFrozen_birthVector (x : ℕ → ℤ) (n k : ℕ) :
    (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset (frozenVertexLabels x n))).map
      (fun v i ↦ birthTime n (v i)) =
        Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset (auxiliarySignTimes x (-1) n)) := by
  have : IsFiniteMeasure (Measure.uniformOfFinset (frozenVertexLabels x n)) := uniformOfFinset_finite _
  rw [Measure.pi_map_pi (fun _ ↦ (measurable_of_countable (birthTime n)).aemeasurable)]
  simp_rw [map_uniformFrozen_birthTime]

/-- Exact distinct-vector law under the frozen-label/birth-time bijection. -/
theorem map_frozenDistinct_birthVector (x : ℕ → ℤ) (n k : ℕ) :
    (frozenDistinctVertexVectorLaw x n k).map (fun v i ↦ birthTime n (v i)) =
      Measure.uniformOfFinset (distinctSampleVectors (auxiliarySignTimes x (-1) n) k) := by
  have hi : Set.InjOn (fun v : Fin k → VertexLabel ↦ fun i ↦ birthTime n (v i))
      (distinctSampleVectors (frozenVertexLabels x n) k : Set (Fin k → VertexLabel)) := by
    intro u hu v hv he
    funext i
    exact birthTime_injOn_frozenVertexLabels x n
      ((mem_distinctSampleVectors.mp hu).1 i)
      ((mem_distinctSampleVectors.mp hv).1 i) (congrFun he i)
  rw [frozenDistinctVertexVectorLaw, map_uniformOfFinset_of_injOn _ _
    (measurable_of_countable _) hi]
  apply congrArg Measure.uniformOfFinset
  apply (image_distinctSampleVectors (frozenVertexLabels x n) (birthTime n)
    (birthTime_injOn_frozenVertexLabels x n) k).trans
  apply congrArg (fun s ↦ distinctSampleVectors s k)
  ext i
  simpa only [Finset.mem_image] using
    (Finset.ext_iff.mp (frozenVertexLabels_image_birthTime x n) i)

/-- The conditioned birth-index law in the local-limit proof is exactly the
iid auxiliary freezing sampler conditioned on distinctness. -/
theorem map_frozenDistinct_birthVector_eq_cond_auxiliary (x : ℕ → ℤ) (n k : ℕ) :
    (frozenDistinctVertexVectorLaw x n k).map (fun v i ↦ birthTime n (v i)) =
      ProbabilityTheory.cond
        (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset (auxiliarySignTimes x (-1) n)))
          {v | Function.Injective v} := by
  rw [map_frozenDistinct_birthVector, cond_pi_uniformOfFinset_distinct]

/-- At every nonempty frozen horizon the auxiliary probability completion is
exactly the normalized actual frozen birth law. -/
theorem map_uniformFrozen_normalizedBirthTime (x : ℕ → ℤ) {n : ℕ}
    (hF : (frozenVertexLabels x n).Nonempty) :
    (Measure.uniformOfFinset (frozenVertexLabels x n)).map
        (fun v ↦ (birthTime n v : ℝ) / n) =
      (auxiliarySignTimeLaw x (-1) n : Measure ℝ) := by
  have hs : (auxiliarySignSteps x (-1) n).Nonempty := by
    rw [frozenVertexLabels_eq] at hF
    obtain ⟨v, hv⟩ := hF
    obtain ⟨i, hi, _⟩ := Finset.mem_map.mp hv
    exact ⟨i, by simpa only [auxiliarySignSteps, downSteps, zero_add] using hi⟩
  rw [auxiliarySignTimeLaw_eq_uniform x (-1) hs, ← map_uniformFrozen_birthTime x n,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

/-- Exact finite-dimensional normalized iid law, with no assumed coupling. -/
theorem map_iidFrozen_normalizedBirthVector (x : ℕ → ℤ) {n : ℕ}
    (hF : (frozenVertexLabels x n).Nonempty) (k : ℕ) :
    (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset (frozenVertexLabels x n))).map
      (fun v i ↦ (birthTime n (v i) : ℝ) / n) =
        (auxiliarySignVectorLaw x (fun _ : Fin k ↦ (-1 : ℤ)) n : Measure (Fin k → ℝ)) := by
  have : IsFiniteMeasure (Measure.uniformOfFinset (frozenVertexLabels x n)) := uniformOfFinset_finite _
  rw [Measure.pi_map_pi (f := fun _ : Fin k ↦ fun v : VertexLabel ↦ (birthTime n v : ℝ) / n)
    (fun _ ↦ (measurable_of_countable _).aemeasurable)]
  simp_rw [map_uniformFrozen_normalizedBirthTime x hF]
  rfl

end Freezing2
