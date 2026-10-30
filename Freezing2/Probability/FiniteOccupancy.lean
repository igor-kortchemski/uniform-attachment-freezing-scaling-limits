module

public import Freezing2.Probability.FiniteDistinctSampling
public import Freezing2.Probability.Bennett
public import Mathlib.Probability.Independence.Basic

/-!
# Actual iid occupancy and repeated values in a finite population

The occupancy count is the number of coordinates in a prescribed subset.
Its Bernoulli laws and independence follow from the actual product measure.
Repeated-value estimates retain the original iid law, and allow the subset
to exclude active labels before a birth-time collision bound is applied.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal BigOperators

namespace Freezing2

variable {A : Type*} [MeasurableSpace A]

noncomputable def sampleOccupancy {k : ℕ} (B : Set A) (v : Fin k → A) : ℕ :=
  (Finset.univ.filter (fun i ↦ v i ∈ B)).card

omit [MeasurableSpace A] in
theorem sampleOccupancy_eq_sum {k : ℕ} (B : Set A) (v : Fin k → A) :
    (sampleOccupancy B v : ℝ) = ∑ i, B.indicator (fun _ ↦ (1 : ℝ)) (v i) := by
  simp only [sampleOccupancy, Set.indicator_apply, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A convenient fixed-ratio lower tail. The larger strict threshold in
Bennett's inequality includes the displayed non-strict occupancy event. -/
theorem iid_sampleOccupancy_lower_tail (μ : Measure A) [IsProbabilityMeasure μ]
    {B : Set A} (hB : MeasurableSet B) (k : ℕ)
    (hm : 0 < (k : ℝ) * μ.real B) :
    (Measure.pi (fun _ : Fin k ↦ μ)).real
      {v | (sampleOccupancy B v : ℝ) ≤ (2 / 3 : ℝ) * (k * μ.real B)} ≤
        Real.exp (-(k * μ.real B) * bennettFunction (1 / 4)) := by
  let p : unitInterval := ⟨μ.real B, measureReal_nonneg, measureReal_le_one⟩
  let Y : Fin k → (Fin k → A) → ℝ := fun i v ↦ B.indicator (fun _ ↦ 1) (v i)
  have hind : iIndepFun Y (Measure.pi (fun _ : Fin k ↦ μ)) := by
    exact iIndepFun_pi (μ := fun _ : Fin k ↦ μ)
      (X := fun _ ↦ B.indicator (fun _ ↦ (1 : ℝ)))
      (fun _ ↦ (measurable_const.indicator hB).aemeasurable)
  have hlaw (i : Fin k) : HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 p)
      (Measure.pi (fun _ : Fin k ↦ μ)) := by
    have heval : HasLaw (fun v : Fin k → A ↦ v i) μ (Measure.pi (fun _ : Fin k ↦ μ)) :=
      ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval (fun _ : Fin k ↦ μ) i).map_eq⟩
    exact (hasLaw_indicator_bernoulliMeasure (1 : ℝ) hB.nullMeasurableSet).comp heval
  have hmean : (∑ _i : Fin k, (p : ℝ)) = k * μ.real B := by simp [p]
  have hm' : 0 < ∑ _i : Fin k, (p : ℝ) := by rwa [hmean]
  have hbound := bennett_lower_tail hind hlaw Finset.univ hm'
    (div_pos hm (by norm_num : (0 : ℝ) < 4))
  rw [hmean] at hbound
  have hquot : (k * μ.real B / 4) / (k * μ.real B) = (1 / 4 : ℝ) := by
    calc
      _ = ((k * μ.real B) / (k * μ.real B)) / 4 := by ring
      _ = _ := by rw [div_self hm.ne']
  rw [hquot] at hbound
  apply (measureReal_mono (fun v hv ↦ ?_)).trans hbound
  simp only [Set.mem_ofPred_eq, Finset.sum_apply]
  change (∑ i, B.indicator (fun _ ↦ (1 : ℝ)) (v i)) <
    k * μ.real B - k * μ.real B / 4
  rw [← sampleOccupancy_eq_sum]
  change (sampleOccupancy B v : ℝ) ≤ (2 / 3 : ℝ) * (k * μ.real B) at hv
  linarith

variable [MeasurableSingletonClass A]

/-- The exact mass of prescribed values at distinct sampled coordinates. -/
theorem pi_uniformOfFinset_equal_coordinates (s : Finset A) (hs : s.Nonempty)
    {k r : ℕ} (j : Fin r ↪ Fin k) {a : A} (ha : a ∈ s) :
    (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s)).real
      {v | ∀ i, v (j i) = a} = (1 / (s.card : ℝ)) ^ r := by
  have := uniformOfFinset_probability_of_nonempty s hs
  have hi := (iIndepFun_pi (μ := fun _ : Fin k ↦ Measure.uniformOfFinset s)
    (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)).precomp j.injective
  have he := hi.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun _ ↦ ({a} : Set A)) (fun _ _ ↦ measurableSet_singleton a)
  have hm (i : Fin r) :
      (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s))
        {v | v (j i) = a} = ((s.card : ℝ≥0∞))⁻¹ := by
    have h := congrArg (fun ν : Measure A ↦ ν {a})
      (measurePreserving_eval (fun _ : Fin k ↦ Measure.uniformOfFinset s) (j i)).map_eq
    rw [Measure.map_apply (measurable_pi_apply _) (measurableSet_singleton _),
      Measure.uniformOfFinset_apply_singleton_of_mem ha] at h
    exact h
  have hevent : (⋂ i ∈ (Finset.univ : Finset (Fin r)),
      (fun v : Fin k → A ↦ v (j i)) ⁻¹' {a}) = {v | ∀ i, v (j i) = a} := by
    ext v
    simp
  change (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s))
    (⋂ i ∈ (Finset.univ : Finset (Fin r)), (fun v : Fin k → A ↦ v (j i)) ⁻¹' {a}) =
      ∏ i : Fin r, (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s))
        {v | v (j i) = a} at he
  rw [hevent] at he
  simp_rw [hm] at he
  simpa [Measure.real] using congrArg ENNReal.toReal he

/-- Some value in the selected subset appears at least `r` times. -/
def repeatedSampleValue (B : Finset A) (k r : ℕ) : Set (Fin k → A) :=
  {v | ∃ j : Fin r ↪ Fin k, ∃ a ∈ B, ∀ i, v (j i) = a}

/-- Union bound over distinct coordinate choices and selected values.
No distinctness or conditioning is imposed on the sampled vector. -/
theorem pi_uniformOfFinset_repeated_value_le (s B : Finset A) (hs : s.Nonempty)
    (hB : B ⊆ s) (k r : ℕ) :
    (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s)).real
      (repeatedSampleValue B k r) ≤
        (k : ℝ) ^ r * B.card / (s.card : ℝ) ^ r := by
  have := uniformOfFinset_probability_of_nonempty s hs
  have he : repeatedSampleValue B k r =
      ⋃ j : Fin r ↪ Fin k, ⋃ a ∈ B, {v | ∀ i, v (j i) = a} := by
    ext v
    simp [repeatedSampleValue]
  rw [he]
  calc
    _ ≤ ∑ j : Fin r ↪ Fin k, (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s)).real
        (⋃ a ∈ B, {v | ∀ i, v (j i) = a}) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ j : Fin r ↪ Fin k, ∑ a ∈ B,
        (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s)).real
          {v | ∀ i, v (j i) = a} :=
      Finset.sum_le_sum (fun j _ ↦ measureReal_biUnion_finset_le B _)
    _ = (k.descFactorial r : ℝ) * B.card / (s.card : ℝ) ^ r := by
      calc
        _ = ∑ _j : Fin r ↪ Fin k, ∑ _a ∈ B, (1 / (s.card : ℝ)) ^ r := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro a ha
          exact pi_uniformOfFinset_equal_coordinates s hs j (hB ha)
        _ = _ := by simp [Fintype.card_embedding_eq, div_eq_mul_inv, mul_assoc]
    _ ≤ _ := by
      gcongr
      exact_mod_cast Nat.descFactorial_le_pow k r

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Without a fourfold repeated selected value, at most three sample
coordinates correspond to each distinct selected label. -/
theorem sampleOccupancy_le_three_mul_image_card [DecidableEq A]
    {k : ℕ} (B : Finset A) (v : Fin k → A)
    (hv : v ∉ repeatedSampleValue B k 4) :
    sampleOccupancy (B : Set A) v ≤
      3 * ((Finset.univ.filter (fun i ↦ v i ∈ B)).image v).card := by
  let J : Finset (Fin k) := Finset.univ.filter (fun i ↦ v i ∈ B)
  have hfiber (a : A) (ha : a ∈ J.image v) : (J.filter (fun i ↦ v i = a)).card ≤ 3 := by
    by_contra h
    have hr : Fintype.card (Fin 4) ≤ (J.filter (fun i ↦ v i = a)).card := by
      simp only [Fintype.card_fin]
      omega
    obtain ⟨j, hj⟩ := Function.Embedding.exists_of_card_le_finset hr
    apply hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨j, v i, (Finset.mem_filter.mp hi).2, ?_⟩
    intro q
    exact (Finset.mem_filter.mp (hj (Set.mem_range_self q))).2
  have hcount : J.card ≤ 3 * (J.image v).card := by
    rw [Finset.card_eq_sum_card_image v J]
    calc
      _ ≤ ∑ _a ∈ J.image v, 3 := Finset.sum_le_sum fun a ha ↦ hfiber a ha
      _ = _ := by simp [mul_comm]
  simpa only [sampleOccupancy, J, Finset.mem_coe] using hcount

end Freezing2
