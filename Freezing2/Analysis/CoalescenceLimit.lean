module

public import Freezing2.Analysis.InteriorMinimumLimit
public import Freezing2.Analysis.LocalCoalescenceIntegrals
public import Freezing2.Analysis.UniformSmallIntervals

/-!
# Uniform local coalescence convergence

This assembles Lemma `lem:hnalpha(v)` with the source's inclusive index interval
and exact limiting endpoints. The finite pairing error, reciprocal-square
correction, local L¹ error, and final mesh-cell error are controlled uniformly.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

/-- The source's inclusive interior integer intervals. -/
def CoalescenceInterval (ε : ℝ) (n a b : ℕ) : Prop :=
  1 ≤ a ∧ a ≤ b ∧ b ≤ n ∧ ε * n ≤ (a : ℝ) ∧ (b : ℝ) ≤ (1 - ε) * n

/-- Local coalescence error with the source's original integration endpoints. -/
noncomputable def coalescenceIntervalError (x : ℕ → ℕ → ℤ) (α : ℝ) (g : ℝ → ℝ)
    (n a b : ℕ) : ℝ :=
  |((n : ℝ) ^ (2 * α) / n) * coalescenceUpSum (x n) (a - 1) (b + 1 - a) -
    (∫ t in Icc ((a : ℝ) / n) ((b : ℝ) / n), (g t) ^ 2) / 2|

/-- The finite maximum is extended by zero on invalid or empty index sets. -/
noncomputable def coalescenceIntervalErrorMax (x : ℕ → ℕ → ℤ) (α : ℝ) (g : ℝ → ℝ)
    (ε : ℝ) (n : ℕ) : ℝ :=
  (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).sup' Finset.univ_nonempty
    (fun p ↦ if CoalescenceInterval ε n p.1.val p.2.val then
      coalescenceIntervalError x α g n p.1.val p.2.val else 0)

/-- The explicit finite estimate, keeping the final one-cell endpoint difference
visible until its uniform absolute-continuity bound is applied. -/
theorem coalescenceIntervalError_bound
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ} (hx : AdmissibleArray x)
    {δ : ℝ} (hδ : 0 < δ) (_hδhalf : δ < 1 / 2)
    (hg2 : IntegrableOn (fun t ↦ (g t) ^ 2) (Icc δ (1 - δ)) volume)
    {N a b : ℕ} (hN : 0 < N) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ N)
    (hstart : δ * N + 1 ≤ (a : ℝ)) (hend : (b : ℝ) + 1 ≤ (1 - δ) * N) :
    coalescenceIntervalError x α g N a b ≤
      (((N : ℝ) ^ α) ^ 2 / N) /
        (activeCount (x N) (interiorMinimizer x N δ (1 - δ)) : ℝ) +
      2 * (∫ t in Icc δ (1 - δ), squareCorrection ((N : ℝ) ^ α)
        (reciprocalProfile x α N t)) +
      (∫ t in Icc δ (1 - δ), |shiftedSquareProfile x α N t - (g t) ^ 2|) / 2 +
      |(∫ t in Icc ((a : ℝ) / N) (((b : ℝ) + 1) / N), (g t) ^ 2) -
        (∫ t in Icc ((a : ℝ) / N) ((b : ℝ) / N), (g t) ^ 2)| / 2 := by
  unfold coalescenceIntervalError
  rw [show 2 * α = α * (2 : ℕ) by ring, Real.rpow_mul_natCast (Nat.cast_nonneg N)]
  let C : ℝ := ((N : ℝ) ^ α) ^ 2 / N
  let K : Set ℝ := Icc δ (1 - δ)
  let J : Set ℝ := Icc ((a : ℝ) / N) (((b : ℝ) + 1) / N)
  let M : ℝ := activeCount (x N) (interiorMinimizer x N δ (1 - δ))
  let p : ℕ := a - 1
  let m : ℕ := b + 1 - a
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpm : p + m = b := by dsimp [p, m]; omega
  have hp1 : (p : ℝ) + 1 = a := by
    dsimp [p]
    exact_mod_cast Nat.sub_add_cancel ha
  have hpm1 : (p : ℝ) + m + 1 = (b : ℝ) + 1 := by exact_mod_cast congrArg Nat.succ hpm
  have hpN : p ≤ N := by omega
  have hsumN : p + m ≤ N := by omega
  have hJ : J ⊆ K := by
    intro t ht
    exact ⟨((le_div_iff₀ hNp).mpr (by linarith)).trans ht.1,
      ht.2.trans ((div_le_iff₀ hNp).mpr hend)⟩
  have hmem (i : ℕ) (hiN : i ≤ N) (hlo : δ * N ≤ (i : ℝ))
      (hhi : (i : ℝ) ≤ (1 - δ) * N) : i ∈ interiorTimes N δ (1 - δ) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hlo, hhi⟩
  have hp_mem : p ∈ interiorTimes N δ (1 - δ) := by
    apply hmem p hpN
    · linarith
    · have hpb : (p : ℝ) ≤ b := by exact_mod_cast (show p ≤ b by omega)
      linarith
  have hb_mem : b ∈ interiorTimes N δ (1 - δ) := by
    apply hmem b hb
    · have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    · linarith
  have hMp : 0 < M := activeCount_real_pos hx N (interiorMinimizer_le x N δ (1 - δ))
  have hminp : M ≤ (activeCount (x N) p : ℝ) := by
    dsimp [M]
    exact_mod_cast interiorMinimizer_min x N δ (1 - δ) hp_mem
  have hminb : M ≤ (activeCount (x N) b : ℝ) := by
    dsimp [M]
    exact_mod_cast interiorMinimizer_min x N δ (1 - δ) hb_mem
  have hip : (activeCount (x N) p : ℝ)⁻¹ ≤ M⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hMp hminp
  have hib : (activeCount (x N) b : ℝ)⁻¹ ≤ M⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hMp hminb
  have hQ : (∫ t in J, shiftedSquareProfile x α N t) =
      C * coalescencePlusSum (x N) p m := by
    simpa only [J, C, hp1, hpm1] using
      (integral_shiftedSquareProfile_one_based (x := x) (α := α) hN p m)
  have hE : (∫ t in J, squareCorrection ((N : ℝ) ^ α) (reciprocalProfile x α N t)) =
      C * coalescenceErrorSum (x N) p m := by
    simpa only [J, C, hp1, hpm1] using
      (integral_squareCorrection_profile_one_based (α := α) hx hN hsumN)
  have hcorr := integrableOn_squareCorrection_profile hx α hN hδ.le
    (show 1 - δ ≤ 1 by linarith)
  have hEc : (∫ t in J, squareCorrection ((N : ℝ) ^ α) (reciprocalProfile x α N t)) ≤
      ∫ t in K, squareCorrection ((N : ℝ) ^ α) (reciprocalProfile x α N t) :=
    setIntegral_mono_set hcorr
      (ae_nonneg_squareCorrection_profile hx α hN hδ.le (by linarith))
      (Eventually.of_forall fun _ ht ↦ hJ ht)
  have hpair := coalescence_uniform_pairing_bound (x N) (hx N).1 (hx N).2 hsumN
  rw [hpm] at hpair
  have hfirst : |C * coalescenceUpSum (x N) p m -
      (∫ t in J, shiftedSquareProfile x α N t) / 2| ≤ C / M +
        2 * (∫ t in K, squareCorrection ((N : ℝ) ^ α) (reciprocalProfile x α N t)) := by
    rw [hQ, show C * coalescenceUpSum (x N) p m -
        C * coalescencePlusSum (x N) p m / 2 =
        C * (coalescenceUpSum (x N) p m - coalescencePlusSum (x N) p m / 2) by ring,
      abs_mul, abs_of_nonneg hC]
    have hp := mul_le_mul_of_nonneg_left hpair hC
    have hm := mul_le_mul_of_nonneg_left (show
      ((activeCount (x N) p : ℝ)⁻¹ + (activeCount (x N) b : ℝ)⁻¹) / 2 ≤ M⁻¹ by linarith) hC
    rw [hE] at hEc
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hsecond : |(∫ t in J, shiftedSquareProfile x α N t) - ∫ t in J, (g t) ^ 2| ≤
      ∫ t in K, |shiftedSquareProfile x α N t - (g t) ^ 2| := by
    have h := abs_setIntegral_sub_le_integral_abs_sub
      (integrableOn_shiftedSquareProfile x α N hδ.le (by linarith)) hg2 J
    have hre : (volume.restrict (Icc δ (1 - δ))).restrict J = volume.restrict J :=
      Measure.restrict_restrict_of_subset hJ
    rw [hre] at h
    exact h
  have ht1 := abs_sub_le (C * coalescenceUpSum (x N) p m)
    ((∫ t in J, shiftedSquareProfile x α N t) / 2)
    ((∫ t in Icc ((a : ℝ) / N) ((b : ℝ) / N), (g t) ^ 2) / 2)
  have ht2 := abs_sub_le ((∫ t in J, shiftedSquareProfile x α N t) / 2)
    ((∫ t in J, (g t) ^ 2) / 2)
    ((∫ t in Icc ((a : ℝ) / N) ((b : ℝ) / N), (g t) ^ 2) / 2)
  simp only [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht1 ht2
  change |C * coalescenceUpSum (x N) p m -
    (∫ t in Icc ((a : ℝ) / N) ((b : ℝ) / N), (g t) ^ 2) / 2| ≤ _
  change _ ≤ C / M + 2 * (∫ t in K,
    squareCorrection ((N : ℝ) ^ α) (reciprocalProfile x α N t)) +
    (∫ t in K, |shiftedSquareProfile x α N t - (g t) ^ 2|) / 2 +
    |(∫ t in J, (g t) ^ 2) -
      (∫ t in Icc ((a : ℝ) / N) ((b : ℝ) / N), (g t) ^ 2)| / 2
  linarith

/-- Uniform epsilon form of Lemma `hnalpha(v)`, including empty or singleton
interior windows and all positive values of the cutoff. -/
theorem eventually_coalescenceIntervalError_lt
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ a b : ℕ, CoalescenceInterval ε n a b →
      coalescenceIntervalError x α g n a b < η := by
  let δ : ℝ := min ε (1 / 4) / 2
  let K : Set ℝ := Icc δ (1 - δ)
  have hδ : 0 < δ := div_pos (lt_min hε (by norm_num)) (by norm_num)
  have hδhalf : δ < 1 / 2 := by
    have h := min_le_right ε (1 / 4)
    dsimp [δ]
    linarith
  have hδε : 2 * δ ≤ ε := by
    have h := min_le_left ε (1 / 4)
    dsimp [δ]
    linarith
  have hδgap : δ < 1 - δ := by linarith
  have hδ1 : 1 - δ < 1 := by linarith
  have hg2 := (h2 δ (1 - δ) hδ hδgap hδ1).1
  have hg0 : ∀ᵐ t ∂profileMeasure, 0 ≤ g t := hpos.mono fun _ ht ↦ ht.le
  let F : ℕ → ℝ := fun n ↦
    (((n : ℝ) ^ α) ^ 2 / n) /
      (activeCount (x n) (interiorMinimizer x n δ (1 - δ)) : ℝ) +
    2 * (∫ t in K, squareCorrection ((n : ℝ) ^ α) (reciprocalProfile x α n t)) +
    (∫ t in K, |shiftedSquareProfile x α n t - (g t) ^ 2|) / 2
  have hmin : Tendsto (fun n : ℕ ↦ (((n : ℝ) ^ α) ^ 2 / n) /
      (activeCount (x n) (interiorMinimizer x n δ (1 - δ)) : ℝ)) atTop (𝓝 0) := by
    apply (tendsto_scaled_reciprocal_interiorMinimum hx hα1 hL1 hpos h2
      hδ hδgap hδ1).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.rpow_sub hn', Real.rpow_one,
      show 2 * α = α * (2 : ℕ) by ring, Real.rpow_mul_natCast hn'.le]
  have hcorr := tendsto_integral_squareCorrection_profile hx hα0 hL1 h2 hg0 hδ hδgap hδ1
  have hshift := tendsto_integral_abs_shiftedSquareProfile_sub_local hx hα0 hL1 h2 hg0
    hδ hδgap hδ1
  have hF : Tendsto F atTop (𝓝 0) := by
    simpa only [F, K, mul_zero, zero_add, zero_div] using
      (hmin.add (hcorr.const_mul 2)).add (hshift.div_const 2)
  have hlarge : ∀ᶠ n : ℕ in atTop, 1 ≤ δ * n := by
    have hn : ∀ᶠ n : ℕ in atTop, 1 / δ ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (1 / δ))
    filter_upwards [hn] with n hn
    have h := (div_le_iff₀ hδ).mp hn
    simpa only [mul_comm] using h
  filter_upwards [hF.eventually_lt_const (show 0 < η / 2 by positivity),
    eventually_uniform_mesh_endpoint_difference_abs_lt hg2 hη, hlarge, eventually_gt_atTop 0]
    with n hFn hcell hnlarge hn0
  intro a b hvalid
  rcases hvalid with ⟨ha, hab, hb, hlow, hupper⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hδεn := mul_le_mul_of_nonneg_right hδε hnpos.le
  have hstart : δ * n + 1 ≤ (a : ℝ) := by nlinarith
  have hend : (b : ℝ) + 1 ≤ (1 - δ) * n := by nlinarith
  have hJ : Icc ((a : ℝ) / n) (((b : ℝ) + 1) / n) ⊆ Icc δ (1 - δ) := by
    intro t ht
    exact ⟨((le_div_iff₀ hnpos).mpr (by linarith)).trans ht.1,
      ht.2.trans ((div_le_iff₀ hnpos).mpr hend)⟩
  have hc := hcell a b hab hJ
  have he := coalescenceIntervalError_bound (α := α) hx hδ hδhalf hg2 hn0 ha hab hb hstart hend
  change coalescenceIntervalError x α g n a b ≤ F n + _ at he
  linarith

theorem coalescenceIntervalErrorMax_nonneg (x : ℕ → ℕ → ℤ) (α : ℝ)
    (g : ℝ → ℝ) (ε : ℝ) (n : ℕ) : 0 ≤ coalescenceIntervalErrorMax x α g ε n := by
  unfold coalescenceIntervalErrorMax
  rw [Finset.le_sup'_iff]
  refine ⟨((0, 0) : Fin (n + 1) × Fin (n + 1)), Finset.mem_univ _, ?_⟩
  simp [CoalescenceInterval]

/-- Lemma `hnalpha(v)` with the full finite maximum, original inclusive sum,
and the source normalization `n^(2α)/n`. -/
theorem tendsto_coalescenceIntervalErrorMax
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (coalescenceIntervalErrorMax x α g ε) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  filter_upwards [eventually_coalescenceIntervalError_lt hx hα0 hα1 hL1 hpos h2 hε hη]
    with n hn
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (coalescenceIntervalErrorMax_nonneg x α g ε n)]
  unfold coalescenceIntervalErrorMax
  rw [Finset.sup'_lt_iff]
  intro p _
  split_ifs with hp
  · exact hn p.1.val p.2.val hp
  · exact hη

end Freezing2
