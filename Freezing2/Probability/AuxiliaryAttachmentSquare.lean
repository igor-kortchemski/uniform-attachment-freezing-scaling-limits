module

public import Freezing2.Probability.AuxiliaryAttachmentRate
public import Freezing2.Analysis.SuccessorSquareProfile

/-!
# The printed squared-denominator auxiliary mark

This records the additional assertion `n/S_(i+1)^2 → g(U)^2` in the proof of
`eq:cv locale`. The statement is joint weak convergence of time and mark; a
joint representation may then be chosen. It makes no claim about marks under
an arbitrary coupling chosen from time convergence alone.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical NNReal ENNReal

namespace Freezing2

/-- The squared-denominator mark printed in the local-limit argument. -/
noncomputable def auxiliaryAttachmentSquare (x : ℕ → ℤ) (n i : ℕ) : ℝ :=
  (n : ℝ) / (activeCount x (i + 1) : ℝ) ^ 2

/-- The complete law of the literal discrete time and squared-denominator mark. -/
noncomputable def auxiliaryAttachmentSquareLaw (x : ℕ → ℤ) (n : ℕ) :
    ProbabilityMeasure (ℝ × ℝ) :=
  (auxiliarySignJitterLaw x 1 n).map
    (fun t ↦ ((⌊(n : ℝ) * t⌋₊ : ℝ) / n, auxiliaryAttachmentSquare x n ⌊(n : ℝ) * t⌋₊))

theorem auxiliaryAttachmentSquareLaw_eq_uniform (x : ℕ → ℤ) {n : ℕ}
    (hs : (auxiliarySignTimes x 1 n).Nonempty) :
    (auxiliaryAttachmentSquareLaw x n : Measure (ℝ × ℝ)) =
      (Measure.uniformOfFinset (auxiliarySignTimes x 1 n)).map
        (fun i : ℕ ↦ ((i : ℝ) / n, auxiliaryAttachmentSquare x n i)) := by
  have hn : 0 < n := by
    obtain ⟨i, hi⟩ := hs
    have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    omega
  have hm : Measurable (fun t : ℝ ↦ ⌊(n : ℝ) * t⌋₊) :=
    (measurable_const.mul measurable_id).nat_floor
  change (meshJitterLaw n (auxiliarySignTimes x 1 n) : Measure ℝ).map _ = _
  rw [← map_meshJitterLaw_floor (s := auxiliarySignTimes x 1 n) hn (Finset.filter_subset _ _) hs,
    Measure.map_map (measurable_of_countable
      (fun i : ℕ ↦ ((i : ℝ) / n, auxiliaryAttachmentSquare x n i))) hm]
  rfl

theorem eventually_auxiliaryAttachmentSquareLaw_eq_uniform
    {x : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray x)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) g) (hpos : PositiveProfile g) :
    ∀ᶠ n in atTop, (auxiliaryAttachmentSquareLaw (x n) n : Measure (ℝ × ℝ)) =
      (Measure.uniformOfFinset (auxiliarySignTimes (x n) 1 n)).map
        (fun i : ℕ ↦ ((i : ℝ) / n, auxiliaryAttachmentSquare (x n) n i)) := by
  have hsign := tendsto_upSteps_measure hx (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos
  filter_upwards [eventually_auxiliarySignTimes_nonempty_of_signMeasure hsign] with n hn
  exact auxiliaryAttachmentSquareLaw_eq_uniform (x n) hn

theorem auxiliaryAttachmentSquare_eq_successorSquareProfile {x : ℕ → ℕ → ℤ}
    {n i : ℕ} (hn : 0 < n) (hi : x n (i + 1) = 1) {t : ℝ}
    (ht : t ∈ profileCell n i) :
    auxiliaryAttachmentSquare (x n) n i = successorSquareProfile x (1 / 2) n t := by
  rw [auxiliaryAttachmentSquare, successorSquareProfile, floor_eq_of_mem_profileCell hn ht,
    activeCount_succ, hi, Int.cast_add, Int.cast_one, div_pow, critical_rpow_sq]

/-- Joint time/squared-mark convergence proves the printed auxiliary-rate
assertion with the original measurable-profile hypotheses. -/
theorem tendsto_auxiliaryAttachmentSquareLaw
    {x : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray x)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x (1 / 2) g) :
    Tendsto (fun n ↦ auxiliaryAttachmentSquareLaw (x n) n) atTop
      (𝓝 (profileProbabilityMeasure.map (fun t ↦ (t, (g t) ^ 2)))) := by
  have hsign := tendsto_upSteps_measure hx (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos
  let μ := fun n ↦ auxiliarySignJitterLaw (x n) 1 n
  have hmarked : Tendsto (fun n ↦ (μ n).map
      (fun t ↦ (t, successorSquareProfile x (1 / 2) n t))) atTop
      (𝓝 (profileProbabilityMeasure.map (fun t ↦ (t, (g t) ^ 2)))) := by
    apply tendsto_marked_profile_of_local_l1_ae (by norm_num : (1 : ℝ≥0) ≤ 4)
      (tendsto_auxiliarySignJitterLaw_of_signMeasure hsign)
      (eventually_auxiliarySignJitterLaw_le hsign)
      (measurable_successorSquareProfile x (1 / 2)) (hL1.1.aemeasurable.pow_const 2)
    · intro a b ha hab hb n
      exact (integrableOn_successorSquareProfile x (1 / 2) n ha.le hb.le).sub (h2 a b ha hab hb).1
    · intro a b ha hab hb
      exact tendsto_integral_abs_successorSquareProfile_sub_local hx
        (by norm_num : (0 : ℝ) < 1 / 2) hL1 h2 (hpos.mono (fun _ ht ↦ ht.le)) ha hab hb
  apply tendsto_probabilityMap_of_error_probability μ
    (F := fun n t ↦ ((⌊(n : ℝ) * t⌋₊ : ℝ) / n,
      auxiliaryAttachmentSquare (x n) n ⌊(n : ℝ) * t⌋₊))
    (G := fun n t ↦ (t, successorSquareProfile x (1 / 2) n t)) ?_ ?_ ?_ hmarked
  · intro n
    have hm : Measurable (fun t : ℝ ↦ ⌊(n : ℝ) * t⌋₊) :=
      (measurable_const.mul measurable_id).nat_floor
    exact (((measurable_of_countable (fun i : ℕ ↦ (i : ℝ))).comp hm).div_const _).prodMk
      ((measurable_of_countable (auxiliaryAttachmentSquare (x n) n)).comp hm)
  · intro n
    exact measurable_id.prodMk (measurable_successorSquareProfile x (1 / 2) n)
  · intro ε hε
    have hi : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    apply tendsto_const_nhds.congr'
    filter_upwards [hi.eventually_lt_const hε, eventually_gt_atTop 0,
      eventually_auxiliarySignTimes_nonempty_of_signMeasure hsign] with n hn hn0 hs
    have hzero : (μ n : Measure ℝ) {t | ε < dist
        ((⌊(n : ℝ) * t⌋₊ : ℝ) / n, auxiliaryAttachmentSquare (x n) n ⌊(n : ℝ) * t⌋₊)
        (t, successorSquareProfile x (1 / 2) n t)} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [ae_mem_meshCells_meshJitterLaw hn0 (Finset.filter_subset _ _) hs] with t ht
      have hd := dist_floor_mesh_lt hn0 ht
      obtain ⟨i, hi, ht⟩ := mem_iUnion₂.mp ht
      have hup := (Finset.mem_filter.mp hi).2
      have hrate := auxiliaryAttachmentSquare_eq_successorSquareProfile hn0 hup ht
      have hfloor := floor_eq_of_mem_profileCell hn0 ht
      rw [hfloor] at hd ⊢
      simp only [hrate, Prod.dist_eq, dist_self]
      refine not_lt_of_ge (max_le_iff.mpr ⟨?_, hε.le⟩)
      simpa only [dist_comm ((i : ℝ) / n) t] using (hd.trans hn).le
    simp only [Measure.real, hzero, ENNReal.toReal_zero]

/-- The printed squared marks also converge for every finite iid family. -/
theorem tendsto_auxiliaryAttachmentSquareLaw_pi
    {x : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray x)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x (1 / 2) g) (k : ℕ) :
    Tendsto (fun n ↦ ProbabilityMeasure.pi (fun _ : Fin k ↦ auxiliaryAttachmentSquareLaw (x n) n))
      atTop (𝓝 (ProbabilityMeasure.pi (fun _ : Fin k ↦
        profileProbabilityMeasure.map (fun t ↦ (t, (g t) ^ 2))))) :=
  ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr (fun _ ↦ tendsto_auxiliaryAttachmentSquareLaw hx hL1 hpos h2))

end Freezing2
