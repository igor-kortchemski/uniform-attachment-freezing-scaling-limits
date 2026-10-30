module

public import Freezing2.Probability.ReverseHistory

/-!
# Conditional transition events on the concrete reverse history

Given the entire exposed prefix, the next transition uses the actual forest
kernel. This is proved from Mathlib's trajectory conditional-expectation theorem.
The event is allowed to depend on both the current and the next forest, covering
both height increments and coalescence hazards.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Freezing2.ReverseHistory

/-- The event involving the current and next forest at construction time `k`. -/
def transitionEvent (E : Set (Forest × Forest)) (k : ℕ) : Set History :=
  {ω | (ω k, ω (k + 1)) ∈ E}

theorem measurableSet_transitionEvent {E : Set (Forest × Forest)}
    (hE : MeasurableSet E) (k : ℕ) : MeasurableSet (transitionEvent E k) :=
  hE.preimage ((measurable_pi_apply k).prodMk (measurable_pi_apply (k + 1)))

/-- A past coordinate is measurable for the sigma algebra of the exposed prefix. -/
theorem measurable_eval_piLE {j k : ℕ} (hj : j ≤ k) :
    Measurable[Filtration.piLE (X := fun _ ↦ Forest) k]
      (fun ω : History ↦ ω j) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_pi_apply (⟨j, Finset.mem_Iic.mpr hj⟩ : Finset.Iic k)).comp
    (comap_measurable (frestrictLe k))

/-- A transition event is known as soon as its next forest has been exposed. -/
theorem measurableSet_transitionEvent_piLE {E : Set (Forest × Forest)}
    (hE : MeasurableSet E) (k : ℕ) :
    MeasurableSet[Filtration.piLE (X := fun _ ↦ Forest) (k + 1)]
      (transitionEvent E k) :=
  hE.preimage ((measurable_eval_piLE (Nat.le_succ k)).prodMk
    (measurable_eval_piLE (le_refl (k + 1))))

/-- Its real indicator, so that conditional probability is conditional expectation. -/
noncomputable def transitionIndicator (E : Set (Forest × Forest)) (k : ℕ) : History → ℝ :=
  (transitionEvent E k).indicator (fun _ ↦ 1)

theorem measurable_transitionIndicator {E : Set (Forest × Forest)}
    (hE : MeasurableSet E) (k : ℕ) : Measurable (transitionIndicator E k) :=
  measurable_const.indicator (measurableSet_transitionEvent hE k)

theorem integrable_transitionIndicator {E : Set (Forest × Forest)}
    (hE : MeasurableSet E) (k : ℕ) (μ : Measure History) [IsProbabilityMeasure μ] :
    Integrable (transitionIndicator E k) μ :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_transitionEvent hE k)

/-- Once the prefix is fixed, the next transition-event probability reduces
to an integral under the actual next-state kernel. -/
theorem integral_transitionIndicator_traj (x : Freezing1.SignSequence) (n k : ℕ)
    {E : Set (Forest × Forest)} (hE : MeasurableSet E) (h : Prefix k) :
    (∫ ω, transitionIndicator E k ω
      ∂Kernel.traj (X := fun _ ↦ Forest) (prefixKernel x n) k h) =
      (stepKernel x n k (last k h)).real {F | (last k h, F) ∈ E} := by
  classical
  let φ : Forest → ℝ := ({F : Forest | (last k h, F) ∈ E}).indicator (fun _ ↦ 1)
  have hφ : Measurable φ := measurable_from_top
  rw [Kernel.integral_traj h (measurable_transitionIndicator hE k).aestronglyMeasurable]
  have hfixed : (fun ω : History ↦ transitionIndicator E k
      (Function.updateFinset ω (Finset.Iic k) h)) = fun ω ↦ φ (ω (k + 1)) := by
    funext ω
    simp [transitionIndicator, transitionEvent, Set.indicator_apply,
      Function.updateFinset, Finset.mem_Iic, φ, last]
  rw [hfixed]
  have hmap : (Kernel.traj (X := fun _ ↦ Forest) (prefixKernel x n) k h).map
      (fun ω ↦ ω (k + 1)) = stepKernel x n k (last k h) := by
    have hm := congrArg (fun K ↦ K h)
      (Kernel.map_traj_succ_self (X := fun _ ↦ Forest) (κ := prefixKernel x n) (a := k))
    simpa only [Kernel.map_apply _ (measurable_pi_apply (k + 1)),
      prefixKernel, Kernel.comap_apply] using hm
  rw [← integral_map (measurable_pi_apply (k + 1)).aemeasurable hφ.aestronglyMeasurable,
    hmap]
  exact integral_indicator_one (by trivial)

/-- The constructed joint law has the claimed conditional transition law given
the entire prefix. No Markov or independence premise is inserted. -/
theorem conditional_transition_indicator (x : Freezing1.SignSequence) (n k : ℕ)
    {E : Set (Forest × Forest)} (hE : MeasurableSet E) :
    (jointLaw x n)[transitionIndicator E k | Filtration.piLE (X := fun _ ↦ Forest) k]
      =ᵐ[jointLaw x n]
      fun ω ↦ (stepKernel x n k (ω k)).real {F | (ω k, F) ∈ E} := by
  have hc := Kernel.condExp_traj (X := fun _ ↦ Forest) (κ := prefixKernel x n)
    (Nat.zero_le k) (x₀ := initialPrefix x n)
    (integrable_transitionIndicator hE k (jointLaw x n))
  refine hc.trans (Eventually.of_forall fun ω ↦ ?_)
  exact integral_transitionIndicator_traj x n k hE (frestrictLe k ω)

/-- An almost sure kernel support property also holds along the constructed
joint history. The premise concerns the actual next-state kernel. -/
theorem jointLaw_ae_transition (x : Freezing1.SignSequence) (n k : ℕ)
    {E : Set (Forest × Forest)} (hE : MeasurableSet E)
    (hkernel : ∀ᵐ ω ∂jointLaw x n,
      stepKernel x n k (ω k) {F | (ω k, F) ∈ E} = 1) :
    ∀ᵐ ω ∂jointLaw x n, (ω k, ω (k + 1)) ∈ E := by
  have hc := conditional_transition_indicator x n k hE
  have hc1 : (jointLaw x n)[transitionIndicator E k |
      Filtration.piLE (X := fun _ ↦ Forest) k] =ᵐ[jointLaw x n] fun _ ↦ (1 : ℝ) := by
    filter_upwards [hc, hkernel] with ω hω hk
    rw [hω, measureReal_def, hk, ENNReal.toReal_one]
  have hi : (∫ ω, transitionIndicator E k ω ∂jointLaw x n) = 1 := by
    rw [← integral_condExp (Filtration.piLE.le k), integral_congr_ae hc1]
    simp
  have hr : (jointLaw x n).real (transitionEvent E k) = 1 := by
    calc
      _ = ∫ ω, transitionIndicator E k ω ∂jointLaw x n :=
        (integral_indicator_one (measurableSet_transitionEvent hE k)).symm
      _ = 1 := hi
  exact (mem_ae_iff_prob_eq_one (measurableSet_transitionEvent hE k)).mpr
    ((ENNReal.toReal_eq_one_iff _).mp hr)

/-- Constant conditional probabilities remain constant after observing any
smaller sigma algebra, in particular a measurable labelled-forest observable. -/
theorem conditional_const_of_le {x : Freezing1.SignSequence} {n k : ℕ}
    {m : MeasurableSpace History} (hm : m ≤ Filtration.piLE (X := fun _ ↦ Forest) k)
    {f : History → ℝ} {p : ℝ}
    (hc : (jointLaw x n)[f | Filtration.piLE (X := fun _ ↦ Forest) k]
      =ᵐ[jointLaw x n] fun _ ↦ p) :
    (jointLaw x n)[f | m] =ᵐ[jointLaw x n] fun _ ↦ p := by
  have ht := condExp_condExp_of_le (μ := jointLaw x n) (f := f) hm
    (Filtration.piLE.le k)
  refine ht.symm.trans ((condExp_congr_ae (m := m) hc).trans ?_)
  rw [condExp_const (hm.trans (Filtration.piLE.le k))]

end Freezing2.ReverseHistory
