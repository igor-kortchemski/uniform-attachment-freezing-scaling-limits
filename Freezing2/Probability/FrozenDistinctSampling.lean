module

public import Freezing2.Probability.DistinctVertexSampling

/-!
# Exact conditioning on frozen distinct vertices

The original iid sampler retains every active vertex. Freezing and distinctness
are explicit conditioning events. Their joint probability tends to one, and the
exact relative normalization is a falling factorial of the frozen count divided
by the full iid population count to the sample-size power.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Classical ENNReal BigOperators

namespace Freezing2

/-- A finite uniform law assigns a contained finite set its exact cardinal ratio. -/
theorem uniformOfFinset_apply_subfinset {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] [DecidableEq A] (s t : Finset A) (ht : t ⊆ s) :
    (Measure.uniformOfFinset s) (t : Set A) = (t.card : ℝ≥0∞) / s.card := by
  rw [Measure.uniformOfFinset_apply]
  simp only [Finset.mem_coe, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr ht]

theorem distinctSampleVectors_subset_pi {A : Type*} {s t : Finset A} (ht : t ⊆ s) (k : ℕ) :
    distinctSampleVectors t k ⊆ Fintype.piFinset (fun _ : Fin k ↦ s) := by
  intro v hv
  exact Fintype.mem_piFinset.mpr fun i ↦ ht ((mem_distinctSampleVectors.mp hv).1 i)

/-- Restricting iid finite samples to distinct vectors from a specified subset
produces precisely uniform sampling without replacement from that subset. -/
theorem cond_pi_uniformOfFinset_subsample_distinct {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] [Countable A] (s t : Finset A) (ht : t ⊆ s) (k : ℕ) :
    ProbabilityTheory.cond (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s))
      (distinctSampleVectors t k : Set (Fin k → A)) =
        Measure.uniformOfFinset (distinctSampleVectors t k) := by
  rw [pi_uniformOfFinset_eq, cond_uniformOfFinset]
  simp only [Finset.mem_coe, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr (distinctSampleVectors_subset_pi ht k)]

/-- Exact probability of distinct sampling from a subset of the population. -/
theorem pi_uniformOfFinset_subsample_distinct {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] [Countable A] (s t : Finset A) (ht : t ⊆ s) (k : ℕ) :
    (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s))
      (distinctSampleVectors t k : Set (Fin k → A)) =
        (t.card.descFactorial k : ℝ≥0∞) / (s.card : ℝ≥0∞) ^ k := by
  rw [pi_uniformOfFinset_eq, uniformOfFinset_apply_subfinset _ _
    (distinctSampleVectors_subset_pi ht k), card_distinctSampleVectors,
    Fintype.card_piFinset_const, Nat.cast_pow]

/-- Actual frozen labels, with their exact one-step birth convention. -/
def frozenVertexLabels (x : ℕ → ℤ) (n : ℕ) : Finset VertexLabel :=
  (vertexLabels x n).filter (fun v ↦ birthTime n v < n)

theorem frozenVertexLabels_subset (x : ℕ → ℤ) (n : ℕ) :
    frozenVertexLabels x n ⊆ vertexLabels x n := Finset.filter_subset _ _

theorem frozenVertexLabels_eq (x : ℕ → ℤ) (n : ℕ) :
    frozenVertexLabels x n = (downSteps x 0 n).map Function.Embedding.inl :=
  early_vertexLabels x le_rfl

theorem frozenVertexLabels_card (x : ℕ → ℤ) (n : ℕ) :
    (frozenVertexLabels x n).card = (downSteps x 0 n).card := by
  rw [frozenVertexLabels_eq, Finset.card_map]

theorem uniformVertex_frozen_mass (x : ℕ → ℤ) (n : ℕ) :
    (uniformVertex x n).real (frozenVertexLabels x n : Set VertexLabel) =
      ((frozenVertexLabels x n).card : ℝ) / (vertexLabels x n).card := by
  rw [Measure.real, uniformVertex, uniformOfFinset_apply_subfinset _ _
    (frozenVertexLabels_subset x n)]
  simp

/-- The mass excluded by requiring a frozen label is exactly `S_n/N_n`. -/
theorem uniformVertex_nonfrozen_mass (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) :
    (uniformVertex x n).real (frozenVertexLabels x n : Set VertexLabel)ᶜ =
      (activeCount x n : ℝ) / (vertexLabels x n).card := by
  have := uniformVertex_isProbabilityMeasure x hx hs
  rw [measureReal_compl (frozenVertexLabels x n).measurableSet, probReal_univ,
    uniformVertex_frozen_mass]
  have hS : ((activeCount x n).toNat : ℝ) = (activeCount x n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hs
  have hcard : ((vertexLabels x n).card : ℝ) =
      ((frozenVertexLabels x n).card : ℝ) + (activeCount x n : ℝ) := by
    rw [frozenVertexLabels_card]
    simp only [vertexLabels, Finset.card_disjSum, Nat.card_Ioc, Nat.sub_zero, Nat.cast_add, hS]
  have hN : ((vertexLabels x n).card : ℝ) ≠ 0 := by
    exact_mod_cast (vertexLabels_nonempty x hx hs).card_pos.ne'
  field_simp
  linarith

/-- The active mass vanishes by the population sublinearity consequence of
`hnalpha(i)`, without deleting it from the original sampling law. -/
theorem tendsto_uniformVertex_nonfrozen_mass
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n ↦ (uniformVertex (x n) n).real
      (frozenVertexLabels (x n) n : Set VertexLabel)ᶜ) atTop (𝓝 0) := by
  have hp := population_sublinear_at hx hα hL1 hpos (a := 1) (by norm_num) le_rfl
  simp only [mul_one, Nat.floor_natCast] at hp
  have h := (hp.const_mul 2).div (tendsto_normalized_vertexLabels_card hx hα hL1 hpos)
    (by norm_num : (1 : ℝ) ≠ 0)
  simp only [mul_zero, zero_div] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [uniformVertex_nonfrozen_mass (x n) (hx n).1 ((hx n).2 n le_rfl).le]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change (2 * ((activeCount (x n) n : ℝ) / n)) /
      ((2 / n) * (vertexLabels (x n) n).card) = _
  rw [show 2 * ((activeCount (x n) n : ℝ) / n) =
    (2 / n) * (activeCount (x n) n : ℝ) by ring]
  exact mul_div_mul_left _ _ (div_ne_zero (by norm_num) hn0)

/-- All prescribed samples are legal frozen labels and are pairwise distinct. -/
noncomputable def frozenDistinctEvent (x : ℕ → ℤ) (n k : ℕ) : Set (Fin k → VertexLabel) :=
  (distinctSampleVectors (frozenVertexLabels x n) k : Set (Fin k → VertexLabel))

noncomputable def frozenDistinctVertexVectorLaw (x : ℕ → ℤ) (n k : ℕ) :
    Measure (Fin k → VertexLabel) :=
  Measure.uniformOfFinset (distinctSampleVectors (frozenVertexLabels x n) k)

theorem frozenDistinctVertexVectorLaw_eq_cond (x : ℕ → ℤ) (n k : ℕ) :
    frozenDistinctVertexVectorLaw x n k =
      ProbabilityTheory.cond (uniformVertexVectorLaw x n k) (frozenDistinctEvent x n k) :=
  (cond_pi_uniformOfFinset_subsample_distinct _ _ (frozenVertexLabels_subset x n) k).symm

theorem uniformVertexVectorLaw_frozenDistinct (x : ℕ → ℤ) (n k : ℕ) :
    (uniformVertexVectorLaw x n k).real (frozenDistinctEvent x n k) =
      ((frozenVertexLabels x n).card.descFactorial k : ℝ) /
        ((vertexLabels x n).card : ℝ) ^ k := by
  rw [Measure.real]
  change ((Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset (vertexLabels x n)))
    (distinctSampleVectors (frozenVertexLabels x n) k : Set (Fin k → VertexLabel))).toReal = _
  rw [pi_uniformOfFinset_subsample_distinct _ _ (frozenVertexLabels_subset x n) k]
  simp


/-- A coordinate of the iid vector has the original vertex law. -/
theorem uniformVertexVectorLaw_coordinate_nonfrozen (x : ℕ → ℤ) (hx : IsSigned x)
    {n k : ℕ} (hs : 0 ≤ activeCount x n) (i : Fin k) :
    (uniformVertexVectorLaw x n k).real {v | v i ∉ frozenVertexLabels x n} =
      (uniformVertex x n).real (frozenVertexLabels x n : Set VertexLabel)ᶜ := by
  have := uniformVertex_isProbabilityMeasure x hx hs
  have hm := (measurePreserving_eval (fun _ : Fin k ↦ uniformVertex x n) i).map_eq
  have h := congrArg (fun μ : Measure VertexLabel ↦
    μ.real (frozenVertexLabels x n : Set VertexLabel)ᶜ) hm
  rw [map_measureReal_apply (measurable_pi_apply i) (frozenVertexLabels x n).measurableSet.compl] at h
  exact h

/-- Failure of the explicit frozen/distinct conditioning has two contributions:
a collision or a sample outside the frozen subset. -/
theorem uniformVertexVectorLaw_frozenDistinct_compl_le (x : ℕ → ℤ) (hx : IsSigned x)
    {n : ℕ} (hs : 0 ≤ activeCount x n) (k : ℕ) :
    (uniformVertexVectorLaw x n k).real (frozenDistinctEvent x n k)ᶜ ≤
      (uniformVertexVectorLaw x n k).real {v | ¬Function.Injective v} +
        k * (uniformVertex x n).real (frozenVertexLabels x n : Set VertexLabel)ᶜ := by
  have := uniformVertexVectorLaw_probability x hx (k := k) hs
  have hsub : (frozenDistinctEvent x n k)ᶜ ⊆
      {v | ¬Function.Injective v} ∪ ⋃ i : Fin k, {v | v i ∉ frozenVertexLabels x n} := by
    intro v hv
    by_cases hinj : Function.Injective v
    · apply Or.inr
      have hnot : ¬∀ i, v i ∈ frozenVertexLabels x n := by
        intro hmem
        exact hv (mem_distinctSampleVectors.mpr ⟨hmem, hinj⟩)
      obtain ⟨i, hi⟩ := not_forall.mp hnot
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · exact Or.inl hinj
  calc
    _ ≤ (uniformVertexVectorLaw x n k).real
        ({v | ¬Function.Injective v} ∪ ⋃ i : Fin k, {v | v i ∉ frozenVertexLabels x n}) :=
      measureReal_mono hsub
    _ ≤ (uniformVertexVectorLaw x n k).real {v | ¬Function.Injective v} +
        (uniformVertexVectorLaw x n k).real (⋃ i : Fin k, {v | v i ∉ frozenVertexLabels x n}) :=
      measureReal_union_le _ _
    _ ≤ (uniformVertexVectorLaw x n k).real {v | ¬Function.Injective v} +
        ∑ i : Fin k, (uniformVertexVectorLaw x n k).real {v | v i ∉ frozenVertexLabels x n} :=
      add_le_add le_rfl (measureReal_iUnion_fintype_le _)
    _ = _ := by simp_rw [uniformVertexVectorLaw_coordinate_nonfrozen x hx hs]; simp

/-- Both conditioning exclusions vanish for fixed sample size under `α < 1`. -/
theorem tendsto_uniformVertexVectorLaw_frozenDistinct_compl
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) (k : ℕ) :
    Tendsto (fun n ↦ (uniformVertexVectorLaw (x n) n k).real
      (frozenDistinctEvent (x n) n k)ᶜ) atTop (𝓝 0) := by
  have h := (tendsto_uniformVertexVectorLaw_collision hx hα hL1 hpos k).add
    ((tendsto_uniformVertex_nonfrozen_mass hx hα hL1 hpos).const_mul (k : ℝ))
  simp only [mul_zero, zero_add] at h
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_ h
  exact Eventually.of_forall fun n ↦
    uniformVertexVectorLaw_frozenDistinct_compl_le (x n) (hx n).1 ((hx n).2 n le_rfl).le k

/-- The actual iid vector is frozen and distinct with probability tending to one. -/
theorem tendsto_uniformVertexVectorLaw_frozenDistinct
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) (k : ℕ) :
    Tendsto (fun n ↦ (uniformVertexVectorLaw (x n) n k).real
      (frozenDistinctEvent (x n) n k)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub
    (tendsto_uniformVertexVectorLaw_frozenDistinct_compl hx hα hL1 hpos k)
  simp only [sub_zero] at h
  apply h.congr
  intro n
  have := uniformVertexVectorLaw_probability (x n) (hx n).1 (k := k) ((hx n).2 n le_rfl).le
  have he := measureReal_add_measureReal_compl (μ := uniformVertexVectorLaw (x n) n k)
    (Set.to_countable (frozenDistinctEvent (x n) n k)).measurableSet
  simpa only [probReal_univ] using (eq_sub_of_add_eq he).symm

/-- Exact relative normalization tends to one, so it can multiply the rescaled
local probabilities without creating an unquantified additive error. -/
theorem tendsto_frozen_distinct_count_ratio
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) (k : ℕ) :
    Tendsto (fun n ↦ ((frozenVertexLabels (x n) n).card.descFactorial k : ℝ) /
      ((vertexLabels (x n) n).card : ℝ) ^ k) atTop (𝓝 1) := by
  simpa only [uniformVertexVectorLaw_frozenDistinct] using
    tendsto_uniformVertexVectorLaw_frozenDistinct hx hα hL1 hpos k

/-- Conditional mass for every prescribed vector of distinct frozen labels. -/
theorem frozenDistinctVertexVectorLaw_singleton (x : ℕ → ℤ) (n k : ℕ)
    (v : Fin k → VertexLabel) (hv : ∀ i, v i ∈ frozenVertexLabels x n)
    (hinj : Function.Injective v) :
    (frozenDistinctVertexVectorLaw x n k) {v} =
      1 / ((k.factorial : ℝ≥0∞) * ((downSteps x 0 n).card.choose k : ℝ≥0∞)) := by
  rw [frozenDistinctVertexVectorLaw, Measure.uniformOfFinset_apply_singleton_of_mem
    (mem_distinctSampleVectors.mpr ⟨hv, hinj⟩), card_distinctSampleVectors,
    frozenVertexLabels_card, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, one_div]

/-- General exact joint conditioning identity on an event contained in the
conditioning support. It also covers a null conditioning event. -/
theorem joint_real_eq_cond_mass_mul {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) (ν : Measure A) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    {D : Set A} (hD : MeasurableSet D) (E : Set (Ω × A))
    (hE : E ⊆ Set.univ ×ˢ D) :
    (μ.prod ν).real E = ν.real D * (μ.prod (ProbabilityTheory.cond ν D)).real E := by
  have h := congrArg ENNReal.toReal (ProbabilityTheory.cond_mul_eq_inter
    (MeasurableSet.univ.prod hD) E (μ.prod ν))
  rw [Set.inter_eq_right.mpr hE, cond_product_right] at h
  simpa only [ENNReal.toReal_mul, Measure.prod_prod, measure_univ, one_mul,
    Measure.real, mul_comm] using h.symm

/-- The corrected finite prefactor for events specifying distinct frozen
samples, in an arbitrary independent random environment such as the reverse history. -/
theorem joint_iid_eq_frozenDistinct_ratio_mul
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ} (hs : 0 ≤ activeCount x n) (k : ℕ)
    (E : Set (Ω × (Fin k → VertexLabel)))
    (hE : ∀ q ∈ E, q.2 ∈ frozenDistinctEvent x n k) :
    (μ.prod (uniformVertexVectorLaw x n k)).real E =
      (((frozenVertexLabels x n).card.descFactorial k : ℝ) /
        ((vertexLabels x n).card : ℝ) ^ k) *
          (μ.prod (frozenDistinctVertexVectorLaw x n k)).real E := by
  have := uniformVertexVectorLaw_probability x hx (k := k) hs
  rw [joint_real_eq_cond_mass_mul μ (uniformVertexVectorLaw x n k)
    (Set.to_countable (frozenDistinctEvent x n k)).measurableSet E
      (fun q hq ↦ ⟨Set.mem_univ _, hE q hq⟩),
    ← frozenDistinctVertexVectorLaw_eq_cond, uniformVertexVectorLaw_frozenDistinct]

end Freezing2
