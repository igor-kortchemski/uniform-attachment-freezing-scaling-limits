module

public import Freezing2.Probability.BranchLengthLimit
public import Freezing2.Probability.SupercriticalCoalescenceLaw

/-!
# The exact late common-birth probability

The paper's U21 assertion uses a closed tail and the minimum of two iid
uniformly sampled birth times. Portmanteau applies because the limiting
uniform law has no atom at the cutoff. Independence gives the square,
without conditioning away repeated samples or active labels.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal Classical

namespace Freezing2

theorem profileMeasure_real_Ici {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    profileMeasure.real (Ici r) = 1 - r := by
  rw [measureReal_def, profileMeasure, Measure.restrict_apply measurableSet_Ici]
  have he : Ici r ∩ Icc (0 : ℝ) 1 = Icc r 1 := by
    ext t
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · exact fun h ↦ ⟨h.1, h.2.2⟩
    · exact fun h ↦ ⟨h.1, hr.trans h.1, h.2⟩
  rw [he, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hr1)]

/-- The closed late-birth tail retains the source endpoint convention. -/
theorem tendsto_uniformVertex_birth_ge
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    Tendsto (fun n ↦ (uniformVertex (x n) n).real
      {v | r * n ≤ (birthTime n v : ℝ)}) atTop (𝓝 (1 - r)) := by
  have hfront : (profileProbabilityMeasure : Measure ℝ) (frontier (Ici r)) = 0 := by
    simp [profileProbabilityMeasure, profileMeasure]
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (tendsto_uniformBirthProbability hx hα hL1 hpos) hfront
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top profileMeasure (Ici r))).comp hlim
  change Tendsto (fun n ↦ (uniformBirthProbability (x n) n (hx n).1
    ((hx n).2 n le_rfl).le : Measure ℝ).real (Ici r)) atTop
      (𝓝 (profileMeasure.real (Ici r))) at hreal
  rw [profileMeasure_real_Ici hr hr1] at hreal
  apply hreal.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [uniformBirthProbability, ProbabilityMeasure.toMeasure_map,
    map_measureReal_apply (measurable_of_countable _) measurableSet_Ici]
  congr 1
  ext v
  simp only [mem_preimage, mem_Ici, mem_ofPred_eq]
  exact le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)

/-- Exact factorization of the common-birth event under the actual sampled
reverse law. Both samples may have the same label. -/
theorem sampledReverseLaw_common_birth_ge (x : ℕ → ℤ) (hx : IsSigned x)
    {n : ℕ} (hs : SurvivesThrough x n) (r : ℝ) :
    (sampledReverseLaw x n).real
      {q | r * n ≤ min (birthTime n q.2.1 : ℝ) (birthTime n q.2.2 : ℝ)} =
      ((uniformVertex x n).real {v | r * n ≤ (birthTime n v : ℝ)}) ^ 2 := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have he : {q : ReverseHistory.History × (VertexLabel × VertexLabel) |
      r * n ≤ min (birthTime n q.2.1 : ℝ) (birthTime n q.2.2 : ℝ)} =
      univ ×ˢ ({v | r * n ≤ (birthTime n v : ℝ)} ×ˢ
        {v | r * n ≤ (birthTime n v : ℝ)}) := by
    ext q
    simp
  rw [he, sampledReverseLaw, measureReal_prod_prod, measureReal_prod_prod]
  simp [sq]

/-- U21: the printed closed common-birth event tends to `δ²`, including
cutoffs zero and one. -/
theorem tendsto_sampledReverseLaw_common_birth_ge
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun n ↦ (sampledReverseLaw (x n) n).real
      {q | (1 - δ) * n ≤ min (birthTime n q.2.1 : ℝ) (birthTime n q.2.2 : ℝ)})
      atTop (𝓝 (δ ^ 2)) := by
  have h := (tendsto_uniformVertex_birth_ge hx hα hL1 hpos
    (r := 1 - δ) (by linarith) (by linarith)).pow 2
  simp only [sub_sub_cancel] at h
  simpa only [sampledReverseLaw_common_birth_ge _ (hx _).1 (hx _).2] using h

/-- The same printed probability under the source's positive-horizon
assumptions, with no extra requirement on row zero. -/
theorem tendsto_sampledReverseLaw_common_birth_ge_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα : α < 1) (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun n ↦ (sampledReverseLaw (x n) n).real
      {q | (1 - δ) * n ≤ min (birthTime n q.2.1 : ℝ) (birthTime n q.2.2 : ℝ)})
      atTop (𝓝 (δ ^ 2)) := by
  apply (tendsto_sampledReverseLaw_common_birth_ge (admissible_initialRowExtension hx)
    hα (hasL1ReciprocalProfile_initialRowExtension hL1)
    (positiveProfile_reciprocal hf) hδ hδ1).congr'
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  rw [hn]

end Freezing2
