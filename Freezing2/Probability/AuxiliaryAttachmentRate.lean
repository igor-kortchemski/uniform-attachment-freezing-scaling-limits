module

public import Freezing2.Probability.AuxiliarySignJitter
public import Freezing2.Probability.MarkedProfileSampling
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Joint auxiliary attachment-time and coalescence-rate convergence

At the paper's zero-based attachment time `i`, the ordered merger factor is
`n / (S_(i+1) (S_(i+1)-1))`. On an attachment step this is exactly
`n / (S_i (S_i+1))`, the shifted-square profile on the preceding mesh cell.
The proof therefore uses the already proved local L1 convergence of that
profile and Lebesgue-dominated jittering. It does not infer convergence of a
measurable sampled rate from weak convergence of times alone.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal Classical

namespace Freezing2

/-- The exact ordered coalescence rate attached to the source time `i`. -/
noncomputable def auxiliaryAttachmentRate (x : ℕ → ℤ) (n i : ℕ) : ℝ :=
  (n : ℝ) / ((activeCount x (i + 1) : ℝ) * ((activeCount x (i + 1) : ℝ) - 1))

/-- A complete probability law for the exact discrete time/rate pair. At every
nonempty attachment horizon it is the finite uniform auxiliary sampler. -/
noncomputable def auxiliaryAttachmentMarkedLaw (x : ℕ → ℤ) (n : ℕ) :
    ProbabilityMeasure (ℝ × ℝ) :=
  (auxiliarySignJitterLaw x 1 n).map
    (fun t ↦ ((⌊(n : ℝ) * t⌋₊ : ℝ) / n, auxiliaryAttachmentRate x n ⌊(n : ℝ) * t⌋₊))

/-- Exact identification with the manuscript's finite uniform time/rate law. -/
theorem auxiliaryAttachmentMarkedLaw_eq_uniform (x : ℕ → ℤ) {n : ℕ}
    (hs : (auxiliarySignTimes x 1 n).Nonempty) :
    (auxiliaryAttachmentMarkedLaw x n : Measure (ℝ × ℝ)) =
      (Measure.uniformOfFinset (auxiliarySignTimes x 1 n)).map
        (fun i : ℕ ↦ ((i : ℝ) / n, auxiliaryAttachmentRate x n i)) := by
  have hn : 0 < n := by
    obtain ⟨i, hi⟩ := hs
    have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    omega
  have hm : Measurable (fun t : ℝ ↦ ⌊(n : ℝ) * t⌋₊) :=
    (measurable_const.mul measurable_id).nat_floor
  change (meshJitterLaw n (auxiliarySignTimes x 1 n) : Measure ℝ).map _ = _
  rw [← map_meshJitterLaw_floor (s := auxiliarySignTimes x 1 n) hn (Finset.filter_subset _ _) hs,
    Measure.map_map (measurable_of_countable
      (fun i : ℕ ↦ ((i : ℝ) / n, auxiliaryAttachmentRate x n i))) hm]
  rfl

/-- Under the source hypotheses, every initial fallback is eventually inactive
and the complete marked law is exactly the uniform attachment-index law. -/
theorem eventually_auxiliaryAttachmentMarkedLaw_eq_uniform
    {x : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray x)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) g) (hpos : PositiveProfile g) :
    ∀ᶠ n in atTop, (auxiliaryAttachmentMarkedLaw (x n) n : Measure (ℝ × ℝ)) =
      (Measure.uniformOfFinset (auxiliarySignTimes (x n) 1 n)).map
        (fun i : ℕ ↦ ((i : ℝ) / n, auxiliaryAttachmentRate (x n) n i)) := by
  have hsign := tendsto_upSteps_measure hx (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos
  filter_upwards [eventually_auxiliarySignTimes_nonempty_of_signMeasure hsign] with n hn
  exact auxiliaryAttachmentMarkedLaw_eq_uniform (x n) hn

theorem critical_rpow_sq (n : ℕ) : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = n := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  norm_num

/-- The zero-based source convention aligns exactly with the preceding cell's
`S(S+1)` profile. No asymptotic endpoint replacement is made. -/
theorem auxiliaryAttachmentRate_eq_shiftedSquareProfile {x : ℕ → ℕ → ℤ}
    {n i : ℕ} (hn : 0 < n) (hi : x n (i + 1) = 1) {t : ℝ}
    (ht : t ∈ profileCell n i) :
    auxiliaryAttachmentRate (x n) n i = shiftedSquareProfile x (1 / 2) n t := by
  rw [auxiliaryAttachmentRate, shiftedSquareProfile, floor_eq_of_mem_profileCell hn ht,
    activeCount_succ, hi, Int.cast_add, Int.cast_one, add_sub_cancel_right, critical_rpow_sq]
  congr 1
  ring

/-- Joint convergence of the actual auxiliary attachment time and its exact
ordered coalescence rate, under the manuscript's critical profile hypotheses. -/
theorem tendsto_auxiliaryAttachmentMarkedLaw
    {x : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray x)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x (1 / 2) g) :
    Tendsto (fun n ↦ auxiliaryAttachmentMarkedLaw (x n) n) atTop
      (𝓝 (profileProbabilityMeasure.map (fun t ↦ (t, (g t) ^ 2)))) := by
  have hsign := tendsto_upSteps_measure hx (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos
  let μ := fun n ↦ auxiliarySignJitterLaw (x n) 1 n
  have hmarked : Tendsto (fun n ↦ (μ n).map
      (fun t ↦ (t, shiftedSquareProfile x (1 / 2) n t))) atTop
      (𝓝 (profileProbabilityMeasure.map (fun t ↦ (t, (g t) ^ 2)))) :=
    tendsto_marked_shiftedSquareProfile hx (by norm_num : (0 : ℝ) < 1 / 2)
      hL1 h2 (hpos.mono (fun _ ht ↦ ht.le)) (by norm_num : (1 : ℝ≥0) ≤ 4)
      (tendsto_auxiliarySignJitterLaw_of_signMeasure hsign)
      (eventually_auxiliarySignJitterLaw_le hsign)
  apply tendsto_probabilityMap_of_error_probability μ
    (F := fun n t ↦ ((⌊(n : ℝ) * t⌋₊ : ℝ) / n,
      auxiliaryAttachmentRate (x n) n ⌊(n : ℝ) * t⌋₊))
    (G := fun n t ↦ (t, shiftedSquareProfile x (1 / 2) n t)) ?_ ?_ ?_ hmarked
  · intro n
    have hm : Measurable (fun t : ℝ ↦ ⌊(n : ℝ) * t⌋₊) :=
      (measurable_const.mul measurable_id).nat_floor
    exact (((measurable_of_countable (fun i : ℕ ↦ (i : ℝ))).comp hm).div_const _).prodMk
      ((measurable_of_countable (auxiliaryAttachmentRate (x n) n)).comp hm)
  · intro n
    exact measurable_id.prodMk (measurable_stepProfile
      (fun i ↦ ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 /
        ((activeCount (x n) i : ℝ) * ((activeCount (x n) i : ℝ) + 1))) n)
  · intro ε hε
    have hi : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    apply tendsto_const_nhds.congr'
    filter_upwards [hi.eventually_lt_const hε, eventually_gt_atTop 0,
      eventually_auxiliarySignTimes_nonempty_of_signMeasure hsign] with n hn hn0 hs
    have hzero : (μ n : Measure ℝ) {t | ε < dist
        ((⌊(n : ℝ) * t⌋₊ : ℝ) / n, auxiliaryAttachmentRate (x n) n ⌊(n : ℝ) * t⌋₊)
        (t, shiftedSquareProfile x (1 / 2) n t)} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [ae_mem_meshCells_meshJitterLaw hn0 (Finset.filter_subset _ _) hs] with t ht
      have hd := dist_floor_mesh_lt hn0 ht
      obtain ⟨i, hi, ht⟩ := mem_iUnion₂.mp ht
      have hup := (Finset.mem_filter.mp hi).2
      have hrate := auxiliaryAttachmentRate_eq_shiftedSquareProfile hn0 hup ht
      have hfloor := floor_eq_of_mem_profileCell hn0 ht
      rw [hfloor] at hd ⊢
      simp only [hrate, Prod.dist_eq, dist_self]
      refine not_lt_of_ge (max_le_iff.mpr ⟨?_, hε.le⟩)
      simpa only [dist_comm ((i : ℝ) / n) t] using (hd.trans hn).le
    simp only [Measure.real, hzero, ENNReal.toReal_zero]

/-- Independent finite vectors of auxiliary time/rate pairs retain their exact
product law and converge jointly, with every fixed number of coordinates. -/
theorem tendsto_auxiliaryAttachmentMarkedLaw_pi
    {x : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray x)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x (1 / 2) g) (k : ℕ) :
    Tendsto (fun n ↦ ProbabilityMeasure.pi (fun _ : Fin k ↦ auxiliaryAttachmentMarkedLaw (x n) n))
      atTop (𝓝 (ProbabilityMeasure.pi (fun _ : Fin k ↦
        profileProbabilityMeasure.map (fun t ↦ (t, (g t) ^ 2))))) :=
  ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr (fun _ ↦ tendsto_auxiliaryAttachmentMarkedLaw hx hL1 hpos h2))

/-- The independent frozen birth times and attachment time/rate pairs converge
jointly. This is the joint law to which a later representation theorem may be
applied; convergence of marks is not inferred from a time-only coupling. -/
theorem tendsto_auxiliary_birth_and_rates
    {x : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray x)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x (1 / 2) g) (b c : ℕ) :
    Tendsto (fun n ↦ (auxiliarySignVectorLaw (x n) (fun _ : Fin b ↦ (-1 : ℤ)) n).prod
      (ProbabilityMeasure.pi (fun _ : Fin c ↦ auxiliaryAttachmentMarkedLaw (x n) n))) atTop
      (𝓝 ((ProbabilityMeasure.pi (fun _ : Fin b ↦ profileProbabilityMeasure)).prod
        (ProbabilityMeasure.pi (fun _ : Fin c ↦
          profileProbabilityMeasure.map (fun t ↦ (t, (g t) ^ 2)))))) := by
  have hB := tendsto_auxiliarySignVectorLaw hx (by norm_num : (1 / 2 : ℝ) < 1)
    hL1 hpos (fun _ : Fin b ↦ (-1 : ℤ)) (fun _ ↦ Or.inr rfl)
  have hC := tendsto_auxiliaryAttachmentMarkedLaw_pi hx hL1 hpos h2 c
  exact ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp (hB.prodMk_nhds hC)

end Freezing2
