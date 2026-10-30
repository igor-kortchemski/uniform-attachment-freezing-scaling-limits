module

public import Freezing2.Probability.AuxiliarySignSampling
public import Freezing2.Analysis.StepProfile

/-!
# Jittering a discrete mesh sampler inside its cells

A uniform choice of mesh index is represented by normalized Lebesgue measure
on the corresponding cells. The floor recovers the exact chosen index, while
the jittered time differs from the left endpoint by less than one mesh width.
This representation supplies a common Lebesgue domination bound for sampling
merely measurable profiles.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical ENNReal NNReal BigOperators

namespace Freezing2

/-- Union of the selected half-open mesh cells. -/
def meshCells (n : ℕ) (s : Finset ℕ) : Set ℝ := ⋃ i ∈ s, profileCell n i

theorem measurableSet_meshCells (n : ℕ) (s : Finset ℕ) : MeasurableSet (meshCells n s) :=
  s.measurableSet_biUnion (fun _ _ ↦ measurableSet_Ico)

theorem meshCells_subset_Icc {n : ℕ} (hn : 0 < n) {s : Finset ℕ}
    (hs : s ⊆ Finset.range n) : meshCells n s ⊆ Icc 0 1 := by
  intro t ht
  have ht' : t ∈ ⋃ i ∈ Finset.range n, profileCell n i := by
    obtain ⟨i, hi, ht⟩ := mem_iUnion₂.mp ht
    exact mem_iUnion₂.mpr ⟨i, hs hi, ht⟩
  rw [profileCells_union hn] at ht'
  exact ⟨ht'.1, ht'.2.le⟩

theorem profileCells_pairwise_any {n : ℕ} (hn : 0 < n) (s : Finset ℕ) :
    PairwiseDisjoint (s : Set ℕ) (profileCell n) := by
  intro i _ j _ hij
  apply Set.disjoint_left.mpr
  intro t hi hj
  exact hij ((floor_eq_of_mem_profileCell hn hi).symm.trans (floor_eq_of_mem_profileCell hn hj))

theorem volume_real_meshCells {n : ℕ} (hn : 0 < n) (s : Finset ℕ) :
    volume.real (meshCells n s) = (s.card : ℝ) / n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [meshCells, measureReal_biUnion_finset (profileCells_pairwise_any hn s)
    (fun _ _ ↦ measurableSet_Ico) (fun _ _ ↦ by simp [profileCell])]
  have hc (i : ℕ) : volume.real (profileCell n i) = 1 / (n : ℝ) := by
    rw [profileCell, Real.volume_real_Ico_of_le (by
      exact div_le_div_of_nonneg_right (by linarith) hn'.le)]
    ring
  simp_rw [hc]
  simp [div_eq_mul_inv]

theorem profileMeasure_real_meshCells {n : ℕ} (hn : 0 < n) {s : Finset ℕ}
    (hs : s ⊆ Finset.range n) : profileMeasure.real (meshCells n s) = (s.card : ℝ) / n := by
  change (volume.restrict (Icc (0 : ℝ) 1)).real (meshCells n s) = _
  rw [measureReal_restrict_apply (measurableSet_meshCells n s),
    inter_eq_left.mpr (meshCells_subset_Icc hn hs), volume_real_meshCells hn]

/-- Restriction of the unit-interval reference measure to selected cells. -/
noncomputable def meshJitterFiniteMeasure (n : ℕ) (s : Finset ℕ) : FiniteMeasure ℝ :=
  ⟨profileMeasure.restrict (meshCells n s), by infer_instance⟩

/-- Probability completion at arbitrary initial horizons; on nonempty legal
mesh sets it is exactly uniform cell jittering. -/
noncomputable def meshJitterLaw (n : ℕ) (s : Finset ℕ) : ProbabilityMeasure ℝ :=
  (meshJitterFiniteMeasure n s).normalize

theorem meshJitterFiniteMeasure_mass {n : ℕ} (hn : 0 < n) {s : Finset ℕ}
    (hs : s ⊆ Finset.range n) :
    ((meshJitterFiniteMeasure n s).mass : ℝ) = (s.card : ℝ) / n := by
  change (profileMeasure.restrict (meshCells n s)).real univ = _
  rw [measureReal_restrict_apply_univ, profileMeasure_real_meshCells hn hs]

theorem meshJitterLaw_eq_smul {n : ℕ} (hn : 0 < n) {s : Finset ℕ}
    (hs : s ⊆ Finset.range n) (hs0 : s.Nonempty) :
    (meshJitterLaw n s : Measure ℝ) =
      ((n : ℝ≥0) / s.card) • profileMeasure.restrict (meshCells n s) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs' : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs0.card_pos.ne'
  have hmass : 0 < ((meshJitterFiniteMeasure n s).mass : ℝ) := by
    rw [meshJitterFiniteMeasure_mass hn hs]
    positivity
  have hne : meshJitterFiniteMeasure n s ≠ 0 := by
    intro h
    simp [h] at hmass
  rw [meshJitterLaw, FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hne]
  have hc : (meshJitterFiniteMeasure n s).mass⁻¹ = (n : ℝ≥0) / s.card := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_inv, NNReal.coe_div, NNReal.coe_natCast,
      meshJitterFiniteMeasure_mass hn hs]
    field_simp
  rw [hc]
  rfl

theorem meshJitterLaw_le {n : ℕ} (hn : 0 < n) {s : Finset ℕ}
    (hs : s ⊆ Finset.range n) (hs0 : s.Nonempty) :
    (meshJitterLaw n s : Measure ℝ) ≤
      (((n : ℝ≥0) / s.card : ℝ≥0) : ℝ≥0∞) • profileMeasure := by
  rw [meshJitterLaw_eq_smul hn hs hs0]
  change (((n : ℝ≥0) / s.card : ℝ≥0) : ℝ≥0∞) •
      profileMeasure.restrict (meshCells n s) ≤ _
  gcongr
  exact Measure.restrict_le_self

theorem meshCells_inter_floor_preimage {n : ℕ} (hn : 0 < n) (s : Finset ℕ) (E : Set ℕ) :
    (fun t : ℝ ↦ ⌊(n : ℝ) * t⌋₊) ⁻¹' E ∩ meshCells n s =
      meshCells n (s.filter (fun i ↦ i ∈ E)) := by
  ext t
  constructor
  · rintro ⟨htE, ht⟩
    obtain ⟨i, hi, ht⟩ := mem_iUnion₂.mp ht
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, by
      simpa only [mem_preimage, floor_eq_of_mem_profileCell hn ht] using htE⟩, ht⟩
  · intro ht
    obtain ⟨i, hi, ht⟩ := mem_iUnion₂.mp ht
    rcases Finset.mem_filter.mp hi with ⟨hi, hiE⟩
    exact ⟨by simpa only [mem_preimage, floor_eq_of_mem_profileCell hn ht] using hiE,
      mem_iUnion₂.mpr ⟨i, hi, ht⟩⟩

/-- Flooring the jittered time recovers the exact finite uniform index law. -/
theorem map_meshJitterLaw_floor {n : ℕ} (hn : 0 < n) {s : Finset ℕ}
    (hs : s ⊆ Finset.range n) (hs0 : s.Nonempty) :
    (meshJitterLaw n s : Measure ℝ).map (fun t ↦ ⌊(n : ℝ) * t⌋₊) =
      Measure.uniformOfFinset s := by
  have : IsFiniteMeasure (Measure.uniformOfFinset s) := uniformOfFinset_finite s
  have hm : Measurable (fun t : ℝ ↦ ⌊(n : ℝ) * t⌋₊) :=
    (measurable_const.mul measurable_id).nat_floor
  apply Measure.ext
  intro E hE
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  change ((meshJitterLaw n s : Measure ℝ).map (fun t ↦ ⌊(n : ℝ) * t⌋₊)).real E = _
  rw [map_measureReal_apply hm hE, meshJitterLaw_eq_smul hn hs hs0,
    measureReal_nnreal_smul_apply, measureReal_restrict_apply (hm hE),
    meshCells_inter_floor_preimage hn,
    profileMeasure_real_meshCells hn (Finset.filter_subset _ _ |>.trans hs),
    Measure.uniformOfFinset_apply]
  simp only [NNReal.coe_div, NNReal.coe_natCast, ENNReal.toReal_div, ENNReal.toReal_natCast]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- The support restriction is retained after normalization. -/
theorem ae_mem_meshCells_meshJitterLaw {n : ℕ} (hn : 0 < n) {s : Finset ℕ}
    (hs : s ⊆ Finset.range n) (hs0 : s.Nonempty) :
    ∀ᵐ t ∂(meshJitterLaw n s : Measure ℝ), t ∈ meshCells n s := by
  rw [ae_iff]
  change (meshJitterLaw n s : Measure ℝ) (meshCells n s)ᶜ = 0
  rw [meshJitterLaw_eq_smul hn hs hs0, Measure.smul_apply,
    Measure.restrict_apply (measurableSet_meshCells n s).compl]
  simp

/-- The jitter lies less than one mesh width from the selected left endpoint. -/
theorem dist_floor_mesh_lt {n : ℕ} (hn : 0 < n) {s : Finset ℕ} {t : ℝ}
    (ht : t ∈ meshCells n s) :
    dist t ((⌊(n : ℝ) * t⌋₊ : ℝ) / n) < 1 / (n : ℝ) := by
  obtain ⟨i, hi, ht⟩ := mem_iUnion₂.mp ht
  rw [floor_eq_of_mem_profileCell hn ht, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
  have he : ((i : ℝ) + 1) / n = (i : ℝ) / n + 1 / (n : ℝ) := by ring
  have h := ht.2
  rw [he] at h
  linarith

end Freezing2
