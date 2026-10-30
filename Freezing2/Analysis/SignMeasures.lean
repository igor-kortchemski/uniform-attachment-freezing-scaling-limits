module

public import Freezing2.Analysis.SignCounts
public import Freezing2.Analysis.IntervalWeakConvergence

/-!
# Weak convergence of attachment and freezing times

The finite measures retain the source's coefficient `2/n` at every horizon.
Their total mass is allowed to differ from one. The proof follows the source:
exact interval counts, sublinear endpoint populations, then Portmanteau.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology BigOperators Classical

namespace Freezing2

/-- The finite measure placing mass `2/n` at each selected mesh time. -/
noncomputable def meshCountingMeasure (n : ℕ) (s : Finset ℕ) : FiniteMeasure ℝ :=
  ⟨(2 / (n : NNReal)) • ∑ i ∈ s, Measure.dirac ((i : ℝ) / n), by infer_instance⟩

/-- Evaluation is exactly the normalized number of selected mesh points in the set. -/
theorem meshCountingMeasure_real (n : ℕ) (s : Finset ℕ) (A : Set ℝ) :
    (meshCountingMeasure n s : Measure ℝ).real A =
      (2 / (n : ℝ)) * (s.filter (fun i : ℕ ↦ (i : ℝ) / n ∈ A)).card := by
  classical
  change ((2 / (n : NNReal)) • ∑ i ∈ s, Measure.dirac ((i : ℝ) / n)).real A = _
  rw [measureReal_nnreal_smul_apply]
  simp only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
  congr 1
  rw [measureReal_def, Measure.finsetSum_apply, ENNReal.toReal_sum (by intros; finiteness)]
  simp only [Measure.dirac_apply, Set.indicator, Pi.one_apply,
    apply_ite ENNReal.toReal, ENNReal.toReal_one, ENNReal.toReal_zero, Finset.sum_boole]

/-- The total mass uses the exact finite-horizon normalization from the source. -/
theorem meshCountingMeasure_mass (n : ℕ) (s : Finset ℕ) :
    ((meshCountingMeasure n s).mass : ℝ) = (2 / (n : ℝ)) * s.card := by
  change (meshCountingMeasure n s : Measure ℝ).real univ = _
  rw [meshCountingMeasure_real]
  simp

/-- The empirical measure of occurrences of one specified sign. -/
noncomputable def signTimeMeasure (x : ℕ → ℤ) (σ : ℤ) (n : ℕ) : FiniteMeasure ℝ :=
  meshCountingMeasure n ((Finset.Ioc 0 n).filter (fun i ↦ x i = σ))

/-- Lebesgue measure on the unit interval, viewed as a finite measure. -/
noncomputable def profileFiniteMeasure : FiniteMeasure ℝ := ⟨profileMeasure, by infer_instance⟩

theorem profileFiniteMeasure_mass : (profileFiniteMeasure.mass : ℝ) = 1 := by
  change (volume.restrict (Icc (0 : ℝ) 1)).real univ = 1
  rw [measureReal_restrict_apply_univ, Real.volume_real_Icc_of_le (by norm_num)]
  norm_num

theorem profileFiniteMeasure_ne_zero : profileFiniteMeasure ≠ 0 := by
  intro h
  have hm := profileFiniteMeasure_mass
  rw [h, FiniteMeasure.zero_mass] at hm
  norm_num at hm

theorem profileFiniteMeasure_real_Iic {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (profileFiniteMeasure : Measure ℝ).real (Iic a) = a := by
  change (volume.restrict (Icc (0 : ℝ) 1)).real (Iic a) = a
  rw [measureReal_restrict_apply measurableSet_Iic]
  have hs : Iic a ∩ Icc 0 1 = Icc 0 a := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · exact fun ht ↦ ⟨ht.2.1, ht.1⟩
    · exact fun ht ↦ ⟨ht.2, ht.1, ht.2.trans ha1⟩
  rw [hs, Real.volume_real_Icc_of_le ha, sub_zero]

theorem profileFiniteMeasure_real_Iic_of_neg {a : ℝ} (ha : a < 0) :
    (profileFiniteMeasure : Measure ℝ).real (Iic a) = 0 := by
  change (volume.restrict (Icc (0 : ℝ) 1)).real (Iic a) = 0
  rw [measureReal_restrict_apply measurableSet_Iic]
  have hs : Iic a ∩ Icc 0 1 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact (not_le_of_gt ha) (ht.2.1.trans ht.1)
  rw [hs]
  simp

theorem profileFiniteMeasure_real_Iic_of_one_le {a : ℝ} (ha : 1 ≤ a) :
    (profileFiniteMeasure : Measure ℝ).real (Iic a) = 1 := by
  change (volume.restrict (Icc (0 : ℝ) 1)).real (Iic a) = 1
  rw [measureReal_restrict_apply measurableSet_Iic]
  have hs : Iic a ∩ Icc 0 1 = Icc 0 1 :=
    inter_eq_right.mpr (fun _ ht ↦ ht.2.trans ha)
  rw [hs, Real.volume_real_Icc_of_le (by norm_num)]
  norm_num

/-- Exact cumulative count inside the unit interval. -/
theorem signTimeMeasure_real_Iic (x : ℕ → ℤ) (σ : ℤ) {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (signTimeMeasure x σ n : Measure ℝ).real (Iic a) =
      (2 / (n : ℝ)) *
        ((Finset.Ioc 0 ⌊(n : ℝ) * a⌋₊).filter (fun i ↦ x i = σ)).card := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloor : ⌊(n : ℝ) * a⌋₊ ≤ n :=
    Nat.floor_le_of_le (by simpa using mul_le_mul_of_nonneg_left ha1 hn'.le)
  rw [signTimeMeasure, meshCountingMeasure_real]
  apply congrArg (fun s : Finset ℕ ↦ (2 / (n : ℝ)) * (s.card : ℝ))
  ext i
  simp only [Finset.mem_filter, Finset.mem_Ioc, mem_Iic]
  have he : (i : ℝ) / n ≤ a ↔ i ≤ ⌊(n : ℝ) * a⌋₊ := by
    rw [div_le_iff₀ hn', Nat.le_floor_iff (mul_nonneg hn'.le ha), mul_comm (n : ℝ) a]
  rw [he]
  constructor
  · exact fun hi ↦ ⟨⟨hi.1.1.1, hi.2⟩, hi.1.2⟩
  · exact fun hi ↦ ⟨⟨⟨hi.1.1, hi.1.2.trans hfloor⟩, hi.2⟩, hi.1.2⟩

theorem signTimeMeasure_real_Iic_of_neg (x : ℕ → ℤ) (σ : ℤ) (n : ℕ)
    {a : ℝ} (ha : a < 0) : (signTimeMeasure x σ n : Measure ℝ).real (Iic a) = 0 := by
  rw [signTimeMeasure, meshCountingMeasure_real]
  apply mul_eq_zero.mpr
  right
  apply Nat.cast_eq_zero.mpr
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i _ hi
  exact (not_le_of_gt ha) ((div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg n)).trans hi)

theorem signTimeMeasure_real_Iic_of_one_le (x : ℕ → ℤ) (σ : ℤ) {n : ℕ}
    (hn : 0 < n) {a : ℝ} (ha : 1 ≤ a) :
    (signTimeMeasure x σ n : Measure ℝ).real (Iic a) =
      ((signTimeMeasure x σ n).mass : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [signTimeMeasure, meshCountingMeasure_real, meshCountingMeasure_mass]
  apply congrArg (fun s : Finset ℕ ↦ (2 / (n : ℝ)) * (s.card : ℝ))
  apply Finset.filter_eq_self.mpr
  intro i hi
  have hi' : i ≤ n := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hi).1).2
  exact ((div_le_one hn').mpr (by exact_mod_cast hi')).trans ha

/-- Cumulative count asymptotics imply the source's finite-measure convergence. -/
theorem tendsto_signTimeMeasure_of_counts {x : ℕ → ℕ → ℤ} (σ : ℤ)
    (hcount : ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      Tendsto (fun n : ℕ ↦ (2 / (n : ℝ)) *
        ((Finset.Ioc 0 ⌊(n : ℝ) * a⌋₊).filter (fun i ↦ x n i = σ)).card)
        atTop (𝓝 a)) :
    Tendsto (fun n ↦ signTimeMeasure (x n) σ n) atTop (𝓝 profileFiniteMeasure) := by
  have hmass : Tendsto (fun n ↦ ((signTimeMeasure (x n) σ n).mass : ℝ))
      atTop (𝓝 1) := by
    simpa only [signTimeMeasure, meshCountingMeasure_mass, mul_one, Nat.floor_natCast]
      using hcount 1 (by norm_num) le_rfl
  apply finiteMeasure_tendsto_of_Iic profileFiniteMeasure_ne_zero
    (by simpa only [profileFiniteMeasure_mass] using hmass)
  intro a
  rcases lt_or_ge a 0 with ha | ha
  · simp only [profileFiniteMeasure_real_Iic_of_neg ha,
      signTimeMeasure_real_Iic_of_neg _ _ _ ha]
    exact tendsto_const_nhds
  · rcases le_or_gt 1 a with ha1 | ha1
    · rw [profileFiniteMeasure_real_Iic_of_one_le ha1]
      apply hmass.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact (signTimeMeasure_real_Iic_of_one_le (x n) σ hn ha1).symm
    · rw [profileFiniteMeasure_real_Iic ha ha1.le]
      apply (hcount a ha ha1.le).congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact (signTimeMeasure_real_Iic (x n) σ hn ha ha1.le).symm

/-- Lemma `lem:hnalpha(ii)` for attachment times. -/
theorem tendsto_upSteps_measure {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n ↦ signTimeMeasure (x n) 1 n) atTop (𝓝 profileFiniteMeasure) := by
  apply tendsto_signTimeMeasure_of_counts
  intro a ha ha1
  simpa only [upSteps, mul_zero, Nat.floor_zero, sub_zero] using
    tendsto_upSteps_macroscopic hx hα hL1 hpos (a := 0) le_rfl ha ha1

/-- Lemma `lem:hnalpha(ii)` for freezing times. -/
theorem tendsto_downSteps_measure {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n ↦ signTimeMeasure (x n) (-1) n) atTop (𝓝 profileFiniteMeasure) := by
  apply tendsto_signTimeMeasure_of_counts
  intro a ha ha1
  simpa only [downSteps, mul_zero, Nat.floor_zero, sub_zero] using
    tendsto_downSteps_macroscopic hx hα hL1 hpos (a := 0) le_rfl ha ha1

end Freezing2
