module

public import Freezing2.Probability.FrozenDistinctSampling
public import Freezing2.Probability.BranchLengthLimit
public import Freezing2.Probability.WeakPerturbation

/-!
# Auxiliary attachment and frozen birth-time samplers

The source uses zero-based times `i - 1` for steps of a prescribed sign.
Normalizing the empirical sign measure and translating by `-1/n` gives the
exact uniform sampler whenever the sign set is nonempty. At empty initial
horizons finite-measure normalization supplies an arbitrary probability law;
the profile hypotheses prove those exceptional horizons eventually disappear.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical ENNReal BigOperators

namespace Freezing2

/-- Source step indices of the prescribed sign. -/
def auxiliarySignSteps (x : ℕ → ℤ) (σ : ℤ) (n : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 n).filter (fun i ↦ x i = σ)

/-- The literal zero-based times in the local coalescent statement. -/
def auxiliarySignTimes (x : ℕ → ℤ) (σ : ℤ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun i ↦ x (i + 1) = σ)

/-- The complete probability law, including an irrelevant initial fallback
when no step of the prescribed sign has yet occurred. -/
noncomputable def auxiliarySignTimeLaw (x : ℕ → ℤ) (σ : ℤ) (n : ℕ) : ProbabilityMeasure ℝ :=
  (signTimeMeasure x σ n).normalize.map (fun t ↦ t - 1 / (n : ℝ))

theorem profileFiniteMeasure_normalize : profileFiniteMeasure.normalize = profileProbabilityMeasure := by
  change profileProbabilityMeasure.toFiniteMeasure.normalize = profileProbabilityMeasure
  exact ProbabilityMeasure.toFiniteMeasure_normalize_eq_self _

/-- Normalization and the one-step translation preserve the uniform weak limit. -/
theorem tendsto_auxiliarySignTimeLaw_of_signMeasure {x : ℕ → ℕ → ℤ} {σ : ℤ}
    (h : Tendsto (fun n ↦ signTimeMeasure (x n) σ n) atTop (𝓝 profileFiniteMeasure)) :
    Tendsto (fun n ↦ auxiliarySignTimeLaw (x n) σ n) atTop (𝓝 profileProbabilityMeasure) := by
  have hn := FiniteMeasure.tendsto_normalize_of_tendsto h profileFiniteMeasure_ne_zero
  rw [profileFiniteMeasure_normalize] at hn
  let μ : ℕ → ProbabilityMeasure ℝ := fun n ↦ (signTimeMeasure (x n) σ n).normalize
  apply tendsto_probabilityMap_of_error_probability μ
    (F := fun n t ↦ t - 1 / (n : ℝ)) (G := fun _ t ↦ t)
    (fun _ ↦ measurable_id.sub_const _) (fun _ ↦ measurable_id) ?_ ?_
  · intro ε hε
    have hi : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    apply tendsto_const_nhds.congr'
    filter_upwards [hi.eventually_lt_const hε] with n hn
    have he : {t : ℝ | ε < dist (t - 1 / (n : ℝ)) t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have hdist : dist (t - 1 / (n : ℝ)) t = 1 / (n : ℝ) := by
        rw [Real.dist_eq, sub_sub_cancel_left, abs_neg,
          abs_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ))]
      change ε < dist (t - 1 / (n : ℝ)) t at ht
      rw [hdist] at ht
      exact (not_lt_of_ge hn.le) ht
    rw [he]
    simp
  · apply hn.congr
    intro n
    apply Subtype.ext
    exact Measure.map_id'.symm

/-- Freezing-time auxiliary samples converge to uniform time, with the exact
`i - 1` convention from the source. -/
theorem tendsto_auxiliaryFreezingTimeLaw
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n ↦ auxiliarySignTimeLaw (x n) (-1) n) atTop (𝓝 profileProbabilityMeasure) :=
  tendsto_auxiliarySignTimeLaw_of_signMeasure (tendsto_downSteps_measure hx hα hL1 hpos)

/-- Attachment-time auxiliary samples have the same uniform limit. -/
theorem tendsto_auxiliaryAttachmentTimeLaw
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n ↦ auxiliarySignTimeLaw (x n) 1 n) atTop (𝓝 profileProbabilityMeasure) :=
  tendsto_auxiliarySignTimeLaw_of_signMeasure (tendsto_upSteps_measure hx hα hL1 hpos)

/-- The auxiliary birth and merger samples are independent across all their
coordinates. A finite index type can contain both kinds of source times. -/
noncomputable def auxiliarySignVectorLaw {ι : Type*} [Fintype ι]
    (x : ℕ → ℤ) (σ : ι → ℤ) (n : ℕ) : ProbabilityMeasure (ι → ℝ) :=
  ProbabilityMeasure.pi (fun i ↦ auxiliarySignTimeLaw x (σ i) n)

theorem tendsto_auxiliarySignVectorLaw {ι : Type*} [Fintype ι]
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (σ : ι → ℤ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1) :
    Tendsto (fun n ↦ auxiliarySignVectorLaw (x n) σ n) atTop
      (𝓝 (ProbabilityMeasure.pi (fun _ : ι ↦ profileProbabilityMeasure))) := by
  apply ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp
  apply tendsto_pi_nhds.mpr
  intro i
  rcases hσ i with hi | hi
  · simpa only [hi] using tendsto_auxiliaryAttachmentTimeLaw hx hα hL1 hpos
  · simpa only [hi] using tendsto_auxiliaryFreezingTimeLaw hx hα hL1 hpos


/-- Normalized empirical counting measure is exactly uniform sampling from its
finite index set, whenever that set and the horizon are nonzero. -/
theorem meshCountingMeasure_normalize_eq_uniform {n : ℕ} (hn : 0 < n)
    (s : Finset ℕ) (hs : s.Nonempty) :
    ((meshCountingMeasure n s).normalize : Measure ℝ) =
      (Measure.uniformOfFinset s).map (fun i : ℕ ↦ (i : ℝ) / n) := by
  have : IsFiniteMeasure (Measure.uniformOfFinset s) := uniformOfFinset_finite s
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsR : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hmass : 0 < ((meshCountingMeasure n s).mass : ℝ) := by
    rw [meshCountingMeasure_mass]
    positivity
  have hne : meshCountingMeasure n s ≠ 0 := by
    intro he
    simp only [he, FiniteMeasure.zero_mass, NNReal.coe_zero] at hmass
    exact lt_irrefl 0 hmass
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hne]
  apply Measure.ext
  intro E hE
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  change (((meshCountingMeasure n s).mass⁻¹ : NNReal) •
    (meshCountingMeasure n s : Measure ℝ)).real E =
      ((Measure.uniformOfFinset s).map (fun i : ℕ ↦ (i : ℝ) / n)).real E
  rw [measureReal_nnreal_smul_apply, NNReal.coe_inv, meshCountingMeasure_mass,
    meshCountingMeasure_real, map_measureReal_apply (measurable_of_countable _) hE]
  change ((2 / (n : ℝ)) * s.card)⁻¹ *
    ((2 / (n : ℝ)) * (s.filter (fun i : ℕ ↦ (i : ℝ) / n ∈ E)).card) =
      ((Measure.uniformOfFinset s) ((fun i : ℕ ↦ (i : ℝ) / n) ⁻¹' E)).toReal
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_preimage, ENNReal.toReal_div, ENNReal.toReal_natCast]
  field_simp

theorem auxiliarySignSteps_image_pred (x : ℕ → ℤ) (σ : ℤ) (n : ℕ) :
    (auxiliarySignSteps x σ n).image (fun i ↦ i - 1) = auxiliarySignTimes x σ n := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rcases Finset.mem_filter.mp hj with ⟨hj, hsign⟩
    rcases Finset.mem_Ioc.mp hj with ⟨hj0, hjn⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), by simpa only [Nat.sub_add_cancel hj0] using hsign⟩
  · intro hi
    rcases Finset.mem_filter.mp hi with ⟨hi, hsign⟩
    apply Finset.mem_image.mpr
    refine ⟨i + 1, ?_, by omega⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by simpa using Finset.mem_range.mp hi⟩,
      hsign⟩

theorem auxiliarySignSteps_pred_injOn (x : ℕ → ℤ) (σ : ℤ) (n : ℕ) :
    Set.InjOn (fun i : ℕ ↦ i - 1) (auxiliarySignSteps x σ n : Set ℕ) := by
  intro i hi j hj he
  have hi0 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hi).1).1
  have hj0 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hj).1).1
  change i - 1 = j - 1 at he
  omega

/-- The completed auxiliary law is exactly the source's zero-based uniform
sign-time law wherever the source sampler is defined. -/
theorem auxiliarySignTimeLaw_eq_uniform (x : ℕ → ℤ) (σ : ℤ) {n : ℕ}
    (hs : (auxiliarySignSteps x σ n).Nonempty) :
    (auxiliarySignTimeLaw x σ n : Measure ℝ) =
      (Measure.uniformOfFinset (auxiliarySignTimes x σ n)).map (fun i : ℕ ↦ (i : ℝ) / n) := by
  have hn : 0 < n := by
    obtain ⟨i, hi⟩ := hs
    have hi' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hi).1
    omega
  have hmem : ∀ᵐ i ∂Measure.uniformOfFinset (auxiliarySignSteps x σ n),
      i ∈ auxiliarySignSteps x σ n := by
    rw [ae_iff, Measure.uniformOfFinset_apply]
    simp
  change (((meshCountingMeasure n (auxiliarySignSteps x σ n)).normalize : Measure ℝ).map
    (fun t ↦ t - 1 / (n : ℝ))) = _
  rw [meshCountingMeasure_normalize_eq_uniform hn _ hs,
    Measure.map_map
      (show Measurable (fun t : ℝ ↦ t - 1 / (n : ℝ)) from measurable_id.sub_const _)
      (measurable_of_countable _)]
  calc
    _ = (Measure.uniformOfFinset (auxiliarySignSteps x σ n)).map
        (fun i : ℕ ↦ ((i - 1 : ℕ) : ℝ) / n) := by
      apply Measure.map_congr
      filter_upwards [hmem] with i hi
      have hi0 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hi).1).1
      simp only [Function.comp_def, Nat.cast_sub hi0, Nat.cast_one]
      ring
    _ = ((Measure.uniformOfFinset (auxiliarySignSteps x σ n)).map (fun i ↦ i - 1)).map
        (fun i : ℕ ↦ (i : ℝ) / n) := by
      rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
      rfl
    _ = _ := by
      rw [map_uniformOfFinset_of_injOn _ _ (measurable_of_countable _)
        (auxiliarySignSteps_pred_injOn x σ n), auxiliarySignSteps_image_pred]

/-- Empty sign sets occur only at irrelevant initial horizons under the profile
hypotheses. This explicitly discharges the fallback in the auxiliary law. -/
theorem eventually_auxiliarySignSteps_nonempty_of_signMeasure {x : ℕ → ℕ → ℤ} {σ : ℤ}
    (h : Tendsto (fun n ↦ signTimeMeasure (x n) σ n) atTop (𝓝 profileFiniteMeasure)) :
    ∀ᶠ n in atTop, (auxiliarySignSteps (x n) σ n).Nonempty := by
  have hm : Tendsto (fun n ↦ ((signTimeMeasure (x n) σ n).mass : ℝ)) atTop (𝓝 1) := by
    simpa only [profileFiniteMeasure_mass] using NNReal.tendsto_coe.mpr h.mass
  filter_upwards [hm.eventually_const_lt (by norm_num : (0 : ℝ) < 1)] with n hn
  by_contra he
  have hcard : (auxiliarySignSteps (x n) σ n).card = 0 :=
    Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp he)
  change 0 < ((meshCountingMeasure n (auxiliarySignSteps (x n) σ n)).mass : ℝ) at hn
  rw [meshCountingMeasure_mass, hcard, Nat.cast_zero, mul_zero] at hn
  exact lt_irrefl 0 hn

theorem eventually_auxiliarySignTimeLaw_eq_uniform
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    ∀ᶠ n in atTop, (auxiliarySignTimeLaw (x n) σ n : Measure ℝ) =
      (Measure.uniformOfFinset (auxiliarySignTimes (x n) σ n)).map (fun i : ℕ ↦ (i : ℝ) / n) := by
  have h : Tendsto (fun n ↦ signTimeMeasure (x n) σ n) atTop (𝓝 profileFiniteMeasure) := by
    rcases hσ with rfl | rfl
    · exact tendsto_upSteps_measure hx hα hL1 hpos
    · exact tendsto_downSteps_measure hx hα hL1 hpos
  filter_upwards [eventually_auxiliarySignSteps_nonempty_of_signMeasure h] with n hn
  exact auxiliarySignTimeLaw_eq_uniform (x n) σ hn

end Freezing2
