module

public import Freezing2.Probability.FiniteDistinctSampling
public import Freezing2.Probability.VertexSampling
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Collision correction for finitely many actual uniform vertices

All source labels, including active vertices, remain in the sampling law.
The collision probability of a fixed iid vector is bounded by `choose(k,2)/N`.
The exact conditional law on distinct vectors is uniform without replacement;
the original iid atom and the conditional atom are kept separate.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Classical ENNReal BigOperators

namespace Freezing2

noncomputable def uniformVertexVectorLaw (x : ℕ → ℤ) (n k : ℕ) :
    Measure (Fin k → VertexLabel) := Measure.pi (fun _ : Fin k ↦ uniformVertex x n)

noncomputable def distinctVertexVectorLaw (x : ℕ → ℤ) (n k : ℕ) :
    Measure (Fin k → VertexLabel) :=
  Measure.uniformOfFinset (distinctSampleVectors (vertexLabels x n) k)

theorem uniformVertexVectorLaw_probability (x : ℕ → ℤ) (hx : IsSigned x) {n k : ℕ}
    (hs : 0 ≤ activeCount x n) : IsProbabilityMeasure (uniformVertexVectorLaw x n k) := by
  have := uniformVertex_isProbabilityMeasure x hx hs
  unfold uniformVertexVectorLaw
  infer_instance

/-- Sampling without replacement is conditioning the actual iid source vector
on distinctness, and does not remove the active-vertex atom. -/
theorem distinctVertexVectorLaw_eq_cond (x : ℕ → ℤ) (n k : ℕ) :
    distinctVertexVectorLaw x n k =
      ProbabilityTheory.cond (uniformVertexVectorLaw x n k) {v | Function.Injective v} :=
  (cond_pi_uniformOfFinset_distinct (vertexLabels x n) k).symm

theorem uniformVertexVectorLaw_singleton (x : ℕ → ℤ) (n k : ℕ) (v : Fin k → VertexLabel)
    (hv : ∀ i, v i ∈ vertexLabels x n) :
    (uniformVertexVectorLaw x n k) {v} = (((vertexLabels x n).card : ℝ≥0∞) ^ k)⁻¹ :=
  pi_uniformOfFinset_singleton (vertexLabels x n) k v hv

theorem distinctVertexVectorLaw_singleton (x : ℕ → ℤ) (n k : ℕ) (v : Fin k → VertexLabel)
    (hv : ∀ i, v i ∈ vertexLabels x n) (hinj : Function.Injective v) :
    (distinctVertexVectorLaw x n k) {v} =
      1 / ((k.factorial : ℝ≥0∞) * ((vertexLabels x n).card.choose k : ℝ≥0∞)) := by
  rw [distinctVertexVectorLaw_eq_cond]
  exact cond_pi_uniformOfFinset_distinct_singleton_choose (vertexLabels x n) k v hv hinj

/-- Distinct sample coordinates have the actual independent two-vertex law;
their sampled values may still coincide. -/
theorem uniformVertexVectorLaw_map_pair (x : ℕ → ℤ) (hx : IsSigned x) {n k : ℕ}
    (hs : 0 ≤ activeCount x n) {i j : Fin k} (hij : i ≠ j) :
    (uniformVertexVectorLaw x n k).map (fun v ↦ (v i, v j)) =
      (uniformVertex x n).prod (uniformVertex x n) := by
  have := uniformVertex_isProbabilityMeasure x hx hs
  have hi := iIndepFun_pi (μ := fun _ : Fin k ↦ uniformVertex x n)
    (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have hm := (hi.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin k ↦ uniformVertex x n) i).map_eq,
    (measurePreserving_eval (fun _ : Fin k ↦ uniformVertex x n) j).map_eq] at hm
  exact hm

theorem uniformVertexVectorLaw_pair_collision (x : ℕ → ℤ) (hx : IsSigned x) {n k : ℕ}
    (hs : 0 ≤ activeCount x n) {i j : Fin k} (hij : i ≠ j) :
    (uniformVertexVectorLaw x n k).real {v | v i = v j} =
      1 / (vertexLabels x n).card := by
  rw [← uniformVertex_collision x hx hs,
    ← uniformVertexVectorLaw_map_pair x hx hs hij,
    map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  rfl

/-- The finite union bound uses each unordered pair exactly once. -/
theorem uniformVertexVectorLaw_collision_le (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) (k : ℕ) :
    (uniformVertexVectorLaw x n k).real {v | ¬Function.Injective v} ≤
      (k.choose 2 : ℝ) / (vertexLabels x n).card := by
  have := uniformVertexVectorLaw_probability x hx (k := k) hs
  let P : Finset (Fin k × Fin k) := (Finset.univ ×ˢ Finset.univ).filter (fun p ↦ p.1 < p.2)
  have hPcard : P.card = k.choose 2 := by
    simpa [P] using Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin k)))
  have he : {v : Fin k → VertexLabel | ¬Function.Injective v} =
      ⋃ p ∈ P, {v | v p.1 = v p.2} := by
    ext v
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hv
      simp only [Function.Injective, not_forall] at hv
      obtain ⟨i, j, hij, hne⟩ := hv
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨(i, j), by simp [P, hlt], hij⟩
      · exact ⟨(j, i), by simp [P, hgt], hij.symm⟩
    · rintro ⟨⟨i, j⟩, hp, heq⟩ hv
      have hij : i < j := (Finset.mem_filter.mp hp).2
      exact hij.ne (hv heq)
  rw [he]
  calc
    _ ≤ ∑ p ∈ P, (uniformVertexVectorLaw x n k).real {v | v p.1 = v p.2} :=
      measureReal_biUnion_finset_le P _
    _ = ∑ _p ∈ P, (1 : ℝ) / (vertexLabels x n).card := by
      apply Finset.sum_congr rfl
      intro p hp
      exact uniformVertexVectorLaw_pair_collision x hx hs (Finset.mem_filter.mp hp).2.ne
    _ = _ := by simp [hPcard, div_eq_mul_inv]

/-- For every fixed sample size, collisions disappear under the source profile
hypotheses. This retains the exact iid model at every finite horizon. -/
theorem tendsto_uniformVertexVectorLaw_collision
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) (k : ℕ) :
    Tendsto (fun n ↦ (uniformVertexVectorLaw (x n) n k).real
      {v | ¬Function.Injective v}) atTop (𝓝 0) := by
  have hbound := (tendsto_uniformVertex_collision hx hα hL1 hpos).const_mul (k.choose 2 : ℝ)
  simp only [mul_zero] at hbound
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_ hbound
  exact Eventually.of_forall fun n ↦ by
    rw [uniformVertex_collision (x n) (hx n).1 ((hx n).2 n le_rfl).le]
    simpa only [div_eq_mul_inv, one_mul] using
      uniformVertexVectorLaw_collision_le (x n) (hx n).1 ((hx n).2 n le_rfl).le k


/-- Exact mass of distinctness under the iid source sampler. -/
theorem uniformVertexVectorLaw_injective (x : ℕ → ℤ) (n k : ℕ) :
    (uniformVertexVectorLaw x n k).real {v | Function.Injective v} =
      ((vertexLabels x n).card.descFactorial k : ℝ) /
        ((vertexLabels x n).card : ℝ) ^ k :=
  pi_uniformOfFinset_real_injective (vertexLabels x n) k

theorem tendsto_uniformVertexVectorLaw_injective
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) (k : ℕ) :
    Tendsto (fun n ↦ (uniformVertexVectorLaw (x n) n k).real
      {v | Function.Injective v}) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub
    (tendsto_uniformVertexVectorLaw_collision hx hα hL1 hpos k)
  simp only [sub_zero] at h
  apply h.congr
  intro n
  have := uniformVertexVectorLaw_probability (x n) (hx n).1 (k := k) ((hx n).2 n le_rfl).le
  have he := measureReal_add_measureReal_compl (μ := uniformVertexVectorLaw (x n) n k)
    (Set.to_countable {v : Fin k → VertexLabel | Function.Injective v}).measurableSet
  simpa only [probReal_univ, Set.compl_ofPred] using (eq_sub_of_add_eq he).symm

/-- The factorial/binomial conditional normalization differs from the iid
normalization by a ratio tending to one. -/
theorem tendsto_vertex_distinct_count_ratio
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) (k : ℕ) :
    Tendsto (fun n ↦ ((vertexLabels (x n) n).card.descFactorial k : ℝ) /
      ((vertexLabels (x n) n).card : ℝ) ^ k) atTop (𝓝 1) := by
  simpa only [uniformVertexVectorLaw_injective] using
    tendsto_uniformVertexVectorLaw_injective hx hα hL1 hpos k

/-- Uniform event-level control of the conditioning correction, eventually
when the distinctness event has positive probability. -/
theorem eventually_distinctVertexVectorLaw_event_error_le
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) (k : ℕ) :
    ∀ᶠ n in atTop, ∀ E : Set (Fin k → VertexLabel),
      |(distinctVertexVectorLaw (x n) n k).real E -
        (uniformVertexVectorLaw (x n) n k).real E| ≤
          (uniformVertexVectorLaw (x n) n k).real {v | ¬Function.Injective v} := by
  filter_upwards [(tendsto_uniformVertexVectorLaw_injective hx hα hL1 hpos k).eventually_const_lt (by norm_num : (0 : ℝ) < 1)] with n hn
  intro E
  have := uniformVertexVectorLaw_probability (x n) (hx n).1 (k := k) ((hx n).2 n le_rfl).le
  have hne : (uniformVertexVectorLaw (x n) n k) {v | Function.Injective v} ≠ 0 := by
    intro he
    change (uniformVertexVectorLaw (x n) n k) {v | Function.Injective v} = 0 at he
    simp only [Measure.real, he, ENNReal.toReal_zero] at hn
    exact lt_irrefl 0 hn
  rw [distinctVertexVectorLaw_eq_cond]
  exact abs_cond_real_sub_le (Set.to_countable _).measurableSet hne E

/-- Any sequence of events may be transferred between the iid and conditioned
without-replacement sampler with a vanishing error. -/
theorem tendsto_distinctVertexVectorLaw_event_difference
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) (k : ℕ)
    (E : ℕ → Set (Fin k → VertexLabel)) :
    Tendsto (fun n ↦ (distinctVertexVectorLaw (x n) n k).real (E n) -
      (uniformVertexVectorLaw (x n) n k).real (E n)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (tendsto_uniformVertexVectorLaw_collision hx hα hL1 hpos k)
  filter_upwards [eventually_distinctVertexVectorLaw_event_error_le hx hα hL1 hpos k] with n hn
  simpa only [Real.norm_eq_abs] using hn (E n)


/-- Conditioning an independent sample coordinate leaves the independent
random environment law unchanged. This also holds for null conditioning. -/
theorem cond_product_right {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (μ : Measure Ω) (ν : Measure B) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (D : Set B) :
    ProbabilityTheory.cond (μ.prod ν) (Set.univ ×ˢ D) =
      μ.prod (ProbabilityTheory.cond ν D) := by
  rw [ProbabilityTheory.cond, Measure.prod_prod, measure_univ, one_mul,
    ProbabilityTheory.cond, Measure.prod_smul_right]
  congr 1
  simpa only [Measure.restrict_univ] using
    (Measure.prod_restrict (μ := μ) (ν := ν) Set.univ D).symm

/-- The collision correction applies uniformly to every event involving one
independent random environment and the complete sampled vector. -/
theorem eventually_joint_distinct_sampling_error_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) (k : ℕ) :
    ∀ᶠ n in atTop, ∀ E : Set (Ω × (Fin k → VertexLabel)),
      |((μ n).prod (distinctVertexVectorLaw (x n) n k)).real E -
        ((μ n).prod (uniformVertexVectorLaw (x n) n k)).real E| ≤
          (uniformVertexVectorLaw (x n) n k).real {v | ¬Function.Injective v} := by
  filter_upwards [(tendsto_uniformVertexVectorLaw_injective hx hα hL1 hpos k).eventually_const_lt
    (by norm_num : (0 : ℝ) < 1)] with n hn
  intro E
  have := uniformVertexVectorLaw_probability (x n) (hx n).1 (k := k) ((hx n).2 n le_rfl).le
  let D : Set (Fin k → VertexLabel) := {v | Function.Injective v}
  have hD : MeasurableSet D := (Set.to_countable _).measurableSet
  have hne : (uniformVertexVectorLaw (x n) n k) D ≠ 0 := by
    intro he
    change (uniformVertexVectorLaw (x n) n k) {v | Function.Injective v} = 0 at he
    simp only [Measure.real, he, ENNReal.toReal_zero] at hn
    exact lt_irrefl 0 hn
  have hneprod : ((μ n).prod (uniformVertexVectorLaw (x n) n k)) (Set.univ ×ˢ D) ≠ 0 := by
    simpa only [Measure.prod_prod, measure_univ, one_mul] using hne
  rw [distinctVertexVectorLaw_eq_cond, ← cond_product_right]
  have h := abs_cond_real_sub_le (MeasurableSet.univ.prod hD) hneprod E
  have hcomp : (Set.univ ×ˢ D)ᶜ = (Set.univ : Set Ω) ×ˢ Dᶜ := by ext q; simp
  have hright : ((μ n).prod (uniformVertexVectorLaw (x n) n k)).real (Set.univ ×ˢ Dᶜ) =
      (uniformVertexVectorLaw (x n) n k).real Dᶜ := by
    simp only [Measure.real, Measure.prod_prod, measure_univ, one_mul]
  rw [hcomp, hright] at h
  exact h

theorem tendsto_joint_distinct_sampling_event_difference
    {Ω : Type*} [MeasurableSpace Ω] (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) (k : ℕ)
    (E : ℕ → Set (Ω × (Fin k → VertexLabel))) :
    Tendsto (fun n ↦ ((μ n).prod (distinctVertexVectorLaw (x n) n k)).real (E n) -
      ((μ n).prod (uniformVertexVectorLaw (x n) n k)).real (E n)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (tendsto_uniformVertexVectorLaw_collision hx hα hL1 hpos k)
  filter_upwards [eventually_joint_distinct_sampling_error_le μ hx hα hL1 hpos k] with n hn
  simpa only [Real.norm_eq_abs] using hn (E n)


/-- On an event that already specifies distinct vertices, the correction is
exactly multiplicative. This identity, unlike a mere additive error estimate,
remains useful after the polynomial rescaling in the source local limit. -/
theorem joint_iid_eq_distinct_ratio_mul
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ} (hs : 0 ≤ activeCount x n) (k : ℕ)
    (E : Set (Ω × (Fin k → VertexLabel))) (hE : ∀ q ∈ E, Function.Injective q.2) :
    (μ.prod (uniformVertexVectorLaw x n k)).real E =
      (((vertexLabels x n).card.descFactorial k : ℝ) / ((vertexLabels x n).card : ℝ) ^ k) *
        (μ.prod (distinctVertexVectorLaw x n k)).real E := by
  have := uniformVertexVectorLaw_probability x hx (k := k) hs
  let D : Set (Fin k → VertexLabel) := {v | Function.Injective v}
  have hD : MeasurableSet D := (Set.to_countable _).measurableSet
  have hDE : (Set.univ ×ˢ D) ∩ E = E := Set.inter_eq_right.mpr (by
    intro q hq
    exact ⟨Set.mem_univ _, hE q hq⟩)
  have h := congrArg ENNReal.toReal (ProbabilityTheory.cond_mul_eq_inter
    (MeasurableSet.univ.prod hD) E (μ.prod (uniformVertexVectorLaw x n k)))
  rw [hDE, cond_product_right] at h
  dsimp only [D] at h
  rw [← distinctVertexVectorLaw_eq_cond] at h
  simp only [ENNReal.toReal_mul] at h
  have hmass : (μ.prod (uniformVertexVectorLaw x n k)).real (Set.univ ×ˢ D) =
      ((vertexLabels x n).card.descFactorial k : ℝ) / ((vertexLabels x n).card : ℝ) ^ k := by
    change ((μ.prod (uniformVertexVectorLaw x n k)) (Set.univ ×ˢ D)).toReal = _
    rw [Measure.prod_prod, measure_univ, one_mul]
    exact uniformVertexVectorLaw_injective x n k
  change ((μ.prod (distinctVertexVectorLaw x n k)) E).toReal *
      ((μ.prod (uniformVertexVectorLaw x n k)) (Set.univ ×ˢ D)).toReal =
      ((μ.prod (uniformVertexVectorLaw x n k)) E).toReal at h
  change (μ.prod (distinctVertexVectorLaw x n k)).real E *
      (μ.prod (uniformVertexVectorLaw x n k)).real (Set.univ ×ˢ D) =
      (μ.prod (uniformVertexVectorLaw x n k)).real E at h
  rw [hmass] at h
  simpa only [mul_comm] using h.symm

end Freezing2
