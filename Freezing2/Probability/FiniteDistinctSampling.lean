module

public import Freezing2.Probability.UniformTransport
public import Mathlib.Probability.UniformOn
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# Iid finite samples and exact conditioning on distinctness

An iid vector is uniform on all vectors in the finite population. Conditioning
on injectivity gives the uniform law on injections; its denominator is the
falling factorial, whereas the unconditional iid atom has denominator `N^k`.
Impossible conditioning events have the library's zero conditional measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace Freezing2

variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]

/-- The finite product of uniform laws is uniform on the finite vector set. -/
theorem pi_uniformOfFinset_eq (s : Finset A) (k : ℕ) :
    Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s) =
      Measure.uniformOfFinset (Fintype.piFinset (fun _ : Fin k ↦ s)) := by
  have : IsFiniteMeasure (Measure.uniformOfFinset s) := uniformOfFinset_finite s
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.pi_singleton, Measure.uniformOfFinset_apply_singleton]
  by_cases hv : ∀ i, v i ∈ s
  · rw [ite_eq_left (Fintype.mem_piFinset.mpr hv)]
    simp only [Measure.uniformOfFinset_apply_singleton_of_mem (hv _),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_piFinset_const,
      Nat.cast_pow, ENNReal.inv_pow]
  · obtain ⟨i, hi⟩ := not_forall.mp hv
    rw [ite_eq_right (fun h ↦ hv (Fintype.mem_piFinset.mp h))]
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (Measure.uniformOfFinset_apply_singleton_of_notMem hi)

/-- The two standard finite uniform-measure definitions coincide. -/
theorem uniformOfFinset_eq_uniformOn (s : Finset A) :
    Measure.uniformOfFinset s = uniformOn (s : Set A) := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.uniformOfFinset_apply_singleton, uniformOn,
    ProbabilityTheory.cond_apply s.measurableSet, Measure.count_apply_finset]
  by_cases ha : a ∈ s
  · simp [ha]
  · simp [ha]

/-- Conditioning a finite uniform law on any event is uniform on the retained
finite subset, including a null conditioning event. -/
theorem cond_uniformOfFinset (s : Finset A) (E : Set A) :
    ProbabilityTheory.cond (Measure.uniformOfFinset s) E =
      Measure.uniformOfFinset (s.filter (fun a ↦ a ∈ E)) := by
  rw [uniformOfFinset_eq_uniformOn, uniformOn,
    ProbabilityTheory.cond_cond_eq_cond_inter' s.measurableSet
      (Set.to_countable E).measurableSet (by simp),
    uniformOfFinset_eq_uniformOn, uniformOn]
  congr 1
  ext a
  simp

/-- Ordered distinct sample vectors from a finite population. -/
noncomputable def distinctSampleVectors (s : Finset A) (k : ℕ) : Finset (Fin k → A) :=
  (Fintype.piFinset (fun _ : Fin k ↦ s)).filter Function.Injective

omit [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A] in
theorem mem_distinctSampleVectors {s : Finset A} {k : ℕ} {v : Fin k → A} :
    v ∈ distinctSampleVectors s k ↔ (∀ i, v i ∈ s) ∧ Function.Injective v := by
  simp only [distinctSampleVectors, Finset.mem_filter, Fintype.mem_piFinset]

omit [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A] in
/-- Exact count of the without-replacement support. -/
theorem card_distinctSampleVectors (s : Finset A) (k : ℕ) :
    (distinctSampleVectors s k).card = s.card.descFactorial k := by
  let e : ↥(distinctSampleVectors s k) ≃ (Fin k ↪ ↥s) :=
    { toFun := fun v ↦
        ⟨fun i ↦ ⟨v.val i, (mem_distinctSampleVectors.mp v.property).1 i⟩,
          fun i j hij ↦ (mem_distinctSampleVectors.mp v.property).2
            (congrArg Subtype.val hij)⟩
      invFun := fun v ↦ ⟨fun i ↦ (v i).val, mem_distinctSampleVectors.mpr
        ⟨fun i ↦ (v i).property, fun i j hij ↦ v.injective (Subtype.ext hij)⟩⟩
      left_inv := fun v ↦ by apply Subtype.ext; rfl
      right_inv := fun v ↦ by ext i; rfl }
  rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_embedding_eq,
    Fintype.card_coe, Fintype.card_fin]

/-- Exact conditional iid/without-replacement relation. -/
theorem cond_pi_uniformOfFinset_distinct (s : Finset A) (k : ℕ) :
    ProbabilityTheory.cond (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s))
        {v | Function.Injective v} =
      Measure.uniformOfFinset (distinctSampleVectors s k) := by
  rw [pi_uniformOfFinset_eq, cond_uniformOfFinset]
  simp only [distinctSampleVectors, Set.mem_ofPred_eq]

/-- Every prescribed legal iid vector, including a vector with repetitions,
has mass `N⁻ᵏ`. -/
theorem pi_uniformOfFinset_singleton (s : Finset A) (k : ℕ) (v : Fin k → A)
    (hv : ∀ i, v i ∈ s) :
    (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s)) {v} =
      ((s.card : ℝ≥0∞) ^ k)⁻¹ := by
  rw [pi_uniformOfFinset_eq, Measure.uniformOfFinset_apply_singleton_of_mem
    (Fintype.mem_piFinset.mpr hv), Fintype.card_piFinset_const, Nat.cast_pow]

/-- Conditional distinct-vector mass has the falling-factorial denominator. -/
theorem cond_pi_uniformOfFinset_distinct_singleton (s : Finset A) (k : ℕ) (v : Fin k → A)
    (hv : ∀ i, v i ∈ s) (hinj : Function.Injective v) :
    (ProbabilityTheory.cond (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s))
      {v | Function.Injective v}) {v} = (s.card.descFactorial k : ℝ≥0∞)⁻¹ := by
  rw [cond_pi_uniformOfFinset_distinct, Measure.uniformOfFinset_apply_singleton_of_mem
    (mem_distinctSampleVectors.mpr ⟨hv, hinj⟩), card_distinctSampleVectors]

/-- The paper's factorial/binomial form is exactly the conditional atom. -/
theorem cond_pi_uniformOfFinset_distinct_singleton_choose (s : Finset A) (k : ℕ)
    (v : Fin k → A) (hv : ∀ i, v i ∈ s) (hinj : Function.Injective v) :
    (ProbabilityTheory.cond (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s))
      {v | Function.Injective v}) {v} =
        1 / ((k.factorial : ℝ≥0∞) * (s.card.choose k : ℝ≥0∞)) := by
  rw [cond_pi_uniformOfFinset_distinct_singleton s k v hv hinj,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, one_div]


/-- Exact distinctness probability, the ratio of without-replacement counts
to the full iid vector count. -/
theorem pi_uniformOfFinset_injective (s : Finset A) (k : ℕ) :
    (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s)) {v | Function.Injective v} =
      (s.card.descFactorial k : ℝ≥0∞) / (s.card : ℝ≥0∞) ^ k := by
  rw [pi_uniformOfFinset_eq, Measure.uniformOfFinset_apply]
  simp only [Set.mem_ofPred_eq]
  change ((distinctSampleVectors s k).card : ℝ≥0∞) / _ = _
  rw [card_distinctSampleVectors, Fintype.card_piFinset_const, Nat.cast_pow]

/-- Real-valued version of the exact distinctness probability. -/
theorem pi_uniformOfFinset_real_injective (s : Finset A) (k : ℕ) :
    (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s)).real
      {v | Function.Injective v} =
        (s.card.descFactorial k : ℝ) / (s.card : ℝ) ^ k := by
  rw [Measure.real, pi_uniformOfFinset_injective]
  simp


/-- Conditioning on an event of positive probability changes every event
probability by at most the probability of the discarded event. -/
theorem abs_cond_real_sub_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D : Set Ω} (hD : MeasurableSet D) (hμD : μ D ≠ 0)
    (E : Set Ω) :
    |(ProbabilityTheory.cond μ D).real E - μ.real E| ≤ μ.real Dᶜ := by
  have := ProbabilityTheory.cond_isProbabilityMeasure (μ := μ) hμD
  have hx0 : 0 ≤ (ProbabilityTheory.cond μ D).real E := measureReal_nonneg
  have hx1 : (ProbabilityTheory.cond μ D).real E ≤ 1 := measureReal_le_one
  have hp : 0 ≤ μ.real Dᶜ := measureReal_nonneg
  have hqp : μ.real D + μ.real Dᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := μ) hD
  have hm : (ProbabilityTheory.cond μ D).real E * μ.real D = μ.real (D ∩ E) := by
    have h := congrArg ENNReal.toReal (ProbabilityTheory.cond_mul_eq_inter hD E μ)
    simpa only [ENNReal.toReal_mul, Measure.real] using h
  have hs : μ.real (D ∩ E) + μ.real (E \ D) = μ.real E := by
    simpa only [Set.inter_comm] using measureReal_inter_add_sdiff (μ := μ) (s := E) hD
  have hz0 : 0 ≤ μ.real (E \ D) := measureReal_nonneg
  have hzp : μ.real (E \ D) ≤ μ.real Dᶜ :=
    measureReal_mono (by intro a ha; exact ha.2)
  have hxp0 := mul_nonneg hx0 hp
  have hxp1 := mul_le_mul_of_nonneg_right hx1 hp
  apply abs_le.mpr
  constructor <;> nlinarith

end Freezing2
