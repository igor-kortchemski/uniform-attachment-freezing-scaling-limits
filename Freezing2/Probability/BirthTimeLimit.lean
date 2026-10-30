module

public import Freezing2.Discrete.Labels
public import Freezing2.Analysis.SignMeasures

/-!
# Uniform birth times converge to the uniform law

This is the sampling consequence of Lemmas `bunif` and `hnalpha(i)` used in
both noncritical regimes. The measure is the pushforward of the actual uniform
measure on the paper's deterministic vertex labels. Frozen births are `i - 1`;
active births are the horizon, so both the shift and the terminal atom are kept.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

/-- The law of normalized birth time, represented as a finite measure. -/
noncomputable def uniformBirthTimeMeasure (x : ℕ → ℤ) (n : ℕ) (hx : IsSigned x)
    (hs : 0 ≤ activeCount x n) : FiniteMeasure ℝ := by
  letI := uniformVertex_isProbabilityMeasure x hx hs
  exact ⟨(uniformVertex x n).map (fun v ↦ (birthTime n v : ℝ) / n),
    (uniformVertex x n).isFiniteMeasure_map _⟩

/-- Normalizing time changes neither the total probability nor the underlying sampling law. -/
theorem uniformBirthTimeMeasure_mass (x : ℕ → ℤ) (n : ℕ) (hx : IsSigned x)
    (hs : 0 ≤ activeCount x n) :
    ((uniformBirthTimeMeasure x n hx hs).mass : ℝ) = 1 := by
  let := uniformVertex_isProbabilityMeasure x hx hs
  change ((uniformVertex x n).map (fun v ↦ (birthTime n v : ℝ) / n)).real univ = 1
  rw [map_measureReal_apply (measurable_of_countable _) MeasurableSet.univ]
  simp

/-- Below time one the cumulative law has exactly the frozen-count numerator,
including the one-step birth shift. -/
theorem uniformBirthTimeMeasure_real_Iic (x : ℕ → ℤ) (hx : IsSigned x)
    {n : ℕ} (hs : 0 ≤ activeCount x n) (hn : 0 < n)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    (uniformBirthTimeMeasure x n hx hs : Measure ℝ).real (Iic a) =
      ((downSteps x 0 (⌊(n : ℝ) * a⌋₊ + 1)).card : ℝ) / (vertexLabels x n).card := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloor : ⌊(n : ℝ) * a⌋₊ < n :=
    Nat.floor_lt (mul_nonneg hn'.le ha) |>.mpr (by nlinarith)
  change ((uniformVertex x n).map (fun v ↦ (birthTime n v : ℝ) / n)).real _ = _
  rw [map_measureReal_apply (measurable_of_countable _) measurableSet_Iic]
  have he : (fun v ↦ (birthTime n v : ℝ) / n) ⁻¹' Iic a =
      {v | birthTime n v < ⌊(n : ℝ) * a⌋₊ + 1} := by
    ext v
    simp only [mem_preimage, mem_Iic, mem_ofPred_eq, Nat.lt_succ_iff]
    rw [div_le_iff₀ hn', Nat.le_floor_iff (mul_nonneg hn'.le ha), mul_comm]
  rw [he, uniformVertex_birth_lt_count x (by omega)]

/-- Advancing the upper counting endpoint adds at most one freezing time. -/
theorem downSteps_card_succ_le (x : ℕ → ℤ) (m : ℕ) :
    (downSteps x 0 m).card ≤ (downSteps x 0 (m + 1)).card ∧
    (downSteps x 0 (m + 1)).card ≤ (downSteps x 0 m).card + 1 := by
  have hsub : downSteps x 0 m ⊆ downSteps x 0 (m + 1) := by
    intro i hi
    simp only [downSteps, Finset.mem_filter, Finset.mem_Ioc] at hi ⊢
    exact ⟨⟨hi.1.1, Nat.le_trans hi.1.2 (Nat.le_succ m)⟩, hi.2⟩
  have hsup : downSteps x 0 (m + 1) ⊆ insert (m + 1) (downSteps x 0 m) := by
    intro i hi
    simp only [downSteps, Finset.mem_filter, Finset.mem_Ioc] at hi
    by_cases he : i = m + 1
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (by
        simp only [downSteps, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hi.1.1, by omega⟩, hi.2⟩))
  exact ⟨Finset.card_le_card hsub,
    (Finset.card_le_card hsup).trans (Finset.card_insert_le _ _)⟩

/-- The frozen birth shift vanishes under the exact counting normalization. -/
theorem tendsto_downSteps_shifted {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Tendsto (fun n : ℕ ↦ (2 / (n : ℝ)) *
      (downSteps (x n) 0 (⌊(n : ℝ) * a⌋₊ + 1)).card) atTop (𝓝 a) := by
  have hl : Tendsto (fun n : ℕ ↦ (2 / (n : ℝ)) *
      (downSteps (x n) 0 ⌊(n : ℝ) * a⌋₊).card) atTop (𝓝 a) := by
    simpa using tendsto_downSteps_macroscopic hx hα hL1 hpos (a := 0)
      (by norm_num) ha ha1
  have he : Tendsto (fun n : ℕ ↦ 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hu := hl.add he
  simp only [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
  · intro n
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (downSteps_card_succ_le
      (x n) ⌊(n : ℝ) * a⌋₊).1) (div_nonneg (by norm_num) (Nat.cast_nonneg n))
  · intro n
    have h := mul_le_mul_of_nonneg_left
      (show ((downSteps (x n) 0 (⌊(n : ℝ) * a⌋₊ + 1)).card : ℝ) ≤
        (downSteps (x n) 0 ⌊(n : ℝ) * a⌋₊).card + 1 by
        exact_mod_cast (downSteps_card_succ_le (x n) ⌊(n : ℝ) * a⌋₊).2)
      (show 0 ≤ 2 / (n : ℝ) by positivity)
    simpa only [mul_add, mul_one] using h

/-- The uniform-vertex normalization has the same limiting factor as sign counts. -/
theorem tendsto_normalized_vertexLabels_card {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n : ℕ ↦ (2 / (n : ℝ)) * (vertexLabels (x n) n).card)
      atTop (𝓝 1) := by
  have hu : Tendsto (fun n : ℕ ↦ (2 / (n : ℝ)) * (upSteps (x n) 0 n).card)
      atTop (𝓝 1) := by
    simpa using tendsto_upSteps_macroscopic hx hα hL1 hpos (a := 0) (b := 1)
      (by norm_num) (by norm_num) le_rfl
  have he : Tendsto (fun n : ℕ ↦ 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [vertexLabels_card _ (hx _).1 ((hx _).2 _ le_rfl).le,
    Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_zero] using hu.add he

/-- Direct evaluation as a uniform finite count. -/
theorem uniformBirthTimeMeasure_real (x : ℕ → ℤ) (n : ℕ) (hx : IsSigned x)
    (hs : 0 ≤ activeCount x n) {A : Set ℝ} (hA : MeasurableSet A) :
    (uniformBirthTimeMeasure x n hx hs : Measure ℝ).real A =
      (((vertexLabels x n).filter (fun v ↦ (birthTime n v : ℝ) / n ∈ A)).card : ℝ) /
        (vertexLabels x n).card := by
  change ((uniformVertex x n).map (fun v ↦ (birthTime n v : ℝ) / n)).real A = _
  rw [map_measureReal_apply (measurable_of_countable _) hA]
  simp only [measureReal_def, uniformVertex, Measure.uniformOfFinset_apply,
    ENNReal.toReal_div, ENNReal.toReal_natCast, mem_preimage]

theorem uniformBirthTimeMeasure_real_Iic_of_neg (x : ℕ → ℤ) (n : ℕ) (hx : IsSigned x)
    (hs : 0 ≤ activeCount x n) {a : ℝ} (ha : a < 0) :
    (uniformBirthTimeMeasure x n hx hs : Measure ℝ).real (Iic a) = 0 := by
  rw [uniformBirthTimeMeasure_real _ _ _ _ measurableSet_Iic]
  have he : (vertexLabels x n).filter (fun v ↦ (birthTime n v : ℝ) / n ∈ Iic a) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro v _ hv
    exact (not_le_of_gt ha) ((div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hv)
  calc
    _ = ((∅ : Finset VertexLabel).card : ℝ) / (vertexLabels x n).card :=
      congrArg (fun s : Finset VertexLabel ↦ (s.card : ℝ) / (vertexLabels x n).card) he
    _ = 0 := by simp

theorem uniformBirthTimeMeasure_real_Iic_of_one_le (x : ℕ → ℤ) (hx : IsSigned x)
    {n : ℕ} (hs : 0 ≤ activeCount x n) (hn : 0 < n) {a : ℝ} (ha : 1 ≤ a) :
    (uniformBirthTimeMeasure x n hx hs : Measure ℝ).real (Iic a) = 1 := by
  rw [uniformBirthTimeMeasure_real _ _ _ _ measurableSet_Iic]
  have he : (vertexLabels x n).filter (fun v ↦ (birthTime n v : ℝ) / n ∈ Iic a) =
      vertexLabels x n := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    exact ((div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
      (by exact_mod_cast birthTime_le x hv)).trans ha
  calc
    _ = ((vertexLabels x n).card : ℝ) / (vertexLabels x n).card :=
      congrArg (fun s : Finset VertexLabel ↦ (s.card : ℝ) / (vertexLabels x n).card) he
    _ = 1 := div_self (Nat.cast_ne_zero.mpr (vertexLabels_nonempty x hx hs).card_pos.ne')

/-- Actual normalized birth-time laws converge weakly to Lebesgue probability
on `[0,1]`. No reverse/forward equality or Skorokhod coupling is assumed. -/
theorem tendsto_uniformBirthTimeMeasure {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n ↦ uniformBirthTimeMeasure (x n) n (hx n).1 ((hx n).2 n le_rfl).le)
      atTop (𝓝 profileFiniteMeasure) := by
  apply finiteMeasure_tendsto_of_Iic profileFiniteMeasure_ne_zero
  · simpa only [uniformBirthTimeMeasure_mass, profileFiniteMeasure_mass] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  · intro a
    by_cases ha : 0 ≤ a
    · by_cases ha1 : a < 1
      · rw [profileFiniteMeasure_real_Iic ha ha1.le]
        have hlim := (tendsto_downSteps_shifted hx hα hL1 hpos ha ha1.le).div
          (tendsto_normalized_vertexLabels_card hx hα hL1 hpos) (by norm_num : (1 : ℝ) ≠ 0)
        simp only [div_one] at hlim
        apply hlim.congr'
        filter_upwards [eventually_gt_atTop 0] with n hn
        rw [uniformBirthTimeMeasure_real_Iic _ _ _ hn ha ha1]
        exact mul_div_mul_left _ _ (div_ne_zero (by norm_num) (by exact_mod_cast hn.ne'))
      · rw [profileFiniteMeasure_real_Iic_of_one_le (le_of_not_gt ha1)]
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_gt_atTop 0] with n hn
        exact (uniformBirthTimeMeasure_real_Iic_of_one_le (x n) (hx n).1
          ((hx n).2 n le_rfl).le hn (le_of_not_gt ha1)).symm
    · simp only [uniformBirthTimeMeasure_real_Iic_of_neg _ _ _ _ (lt_of_not_ge ha),
        profileFiniteMeasure_real_Iic_of_neg (lt_of_not_ge ha)]
      exact tendsto_const_nhds

end Freezing2
