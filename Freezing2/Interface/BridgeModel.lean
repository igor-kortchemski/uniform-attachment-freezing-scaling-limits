module

public import Freezing2.Interface.Defs
public import Freezing2.Probability.CompanionModel
public import Freezing2.Probability.CanonicalMetricTransport
public import Freezing2.Probability.SampledTreeTransport
public import Freezing2.Probability.BranchLengthLimit
public import Freezing2.Probability.SupercriticalSourceMatrix
public import Freezing2.Analysis.CriticalPopulationBound

/-!
# Bridge between the interface model and the library model

The interface state `FreezingStatements.TreeState` keeps the vertices, the
active vertices and the edges of Algorithm 1. The library state
`Freezing1.Forward.State` also records parents, heights and freezing labels.
Forgetting these fields commutes with every legal step, so the interface tree
law is the image of the library tree law (`treeLaw_eq_map`). Heights, sampled
distance matrices and the hypotheses on the driving array correspond exactly.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace FreezingStatements.Bridge

/-- Forget the bookkeeping fields of a library state. -/
def forget (s : Freezing1.Forward.State) : TreeState := ⟨s.vertices, s.active, s.graph⟩

theorem measurable_forget : Measurable forget := measurable_from_top

theorem ae_mem_uniformOfFinset {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (A : Finset α) :
    ∀ᵐ v ∂Measure.uniformOfFinset A, v ∈ A := by
  classical
  rw [ae_iff, Measure.uniformOfFinset_apply]
  simp

/-- One interface step is the image of one library step. -/
theorem transitionLaw_forget (s : Freezing1.Forward.State) (t : ℕ) (ε : ℤ) :
    transitionLaw (forget s) t ε =
      (Freezing1.Forward.transitionLaw s t (decide (ε = 1))).map forget := by
  unfold transitionLaw Freezing1.Forward.transitionLaw
  by_cases h : s.active.Nonempty
  · rw [ite_eq_left (show (forget s).active.Nonempty from h), ite_eq_left h,
      Measure.map_map measurable_forget measurable_from_top]
    apply Measure.map_congr
    filter_upwards [ae_mem_uniformOfFinset s.active] with v hv
    by_cases hε : ε = 1
    · simp [step, Freezing1.Forward.step, hv, hε, forget, Freezing1.Forward.attach]
    · simp [step, Freezing1.Forward.step, hv, hε, forget, Freezing1.Forward.freeze]
  · rw [ite_eq_right (show ¬(forget s).active.Nonempty from h), ite_eq_right h,
      Measure.map_dirac' measurable_forget]

/-- The interface tree law is the image of the library tree law. -/
theorem treeLaw_eq_map (x : ℕ → ℤ) (n : ℕ) :
    treeLaw x n = (Freezing1.Forward.treeLaw (Freezing2.companionSchedule x) n).map forget := by
  induction n with
  | zero =>
    rw [treeLaw, Freezing1.Forward.treeLaw, Measure.map_dirac' measurable_forget]
    rfl
  | succ n ih =>
    rw [treeLaw, Freezing1.Forward.treeLaw, ih,
      Measure.bind_map measurable_forget.aemeasurable measurable_from_top.aemeasurable,
      Measure.map_bind measurable_from_top.aemeasurable measurable_forget.aemeasurable]
    congr 1
    funext s
    exact transitionLaw_forget s (n + 1) (x (n + 1))

theorem treeLaw_eq_map_freezingTreeLaw (x : ℕ → ℕ → ℤ) (n : ℕ) :
    treeLaw (x n) n = (Freezing2.freezingTreeLaw x n).map forget :=
  treeLaw_eq_map (x n) n

/-- On valid states, the interface height is the library height. -/
theorem height_forget {n : ℕ} {s : Freezing1.Forward.State}
    (hs : Freezing1.Forward.ValidAt n s) :
    height (forget s) = Freezing1.Forward.treeHeight s := by
  unfold height Freezing1.Forward.treeHeight
  apply Finset.sup_congr rfl
  intro v hv
  exact ((hs.height_eq_tree_dist ⟨v, hv⟩).trans
    (Freezing2.forward_tree_dist_eq hs ⟨0, hs.root_mem⟩ ⟨v, hv⟩)).symm

/-! ## Hypotheses -/

theorem isSigned_iff (x : ℕ → ℤ) : IsSigned x ↔ Freezing2.IsSigned x := Iff.rfl

theorem activeCount_eq (x : ℕ → ℤ) (k : ℕ) : activeCount x k = Freezing2.activeCount x k := rfl

theorem survivesThrough_iff (x : ℕ → ℤ) (n : ℕ) :
    SurvivesThrough x n ↔ Freezing2.SurvivesThrough x n := Iff.rfl

theorem hasL1ReciprocalProfile_iff (x : ℕ → ℕ → ℤ) (α : ℝ) (g : ℝ → ℝ) :
    HasL1ReciprocalProfile x α g ↔ Freezing2.HasL1ReciprocalProfile x α g := Iff.rfl

theorem hasLocalSquareMomentProfile_iff (x : ℕ → ℕ → ℤ) (α : ℝ) (g : ℝ → ℝ) :
    HasLocalSquareMomentProfile x α g ↔ Freezing2.HasLocalSquareMomentProfile x α g := Iff.rfl

theorem rowMaxPopulation_eq (x : ℕ → ℤ) (n : ℕ) :
    rowMaxPopulation x n = Freezing2.rowMaxPopulation x n := rfl

/-- The interface height scale is the companion height scale. -/
theorem upHarmonicSum_eq (x : ℕ → ℤ) (hx : Freezing2.IsSigned x) (n : ℕ) :
    upHarmonicSum x n = Freezing1.heightScale (Freezing2.companionSchedule x) n := by
  rw [Freezing2.companion_heightScale x hx, Freezing2.harmonicUpInterval, upHarmonicSum,
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, zero_add, one_div, activeCount_eq]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [add_comm 1 i]

/-! ## Sampled distance matrices -/

/-- The interface sampled-distance law is the library one. -/
theorem sampledDistanceLaw_eq (x : ℕ → ℤ) (α : ℝ) (n k : ℕ) :
    sampledDistanceLaw x α n k =
      (Freezing2.TreeSampling.forwardSampledDistanceLaw (Freezing2.companionSchedule x) α n k :
        Measure (Fin (k + 1) → Fin (k + 1) → ℝ)) := by
  rw [sampledDistanceLaw, treeLaw_eq_map,
    Measure.bind_map measurable_forget.aemeasurable measurable_from_top.aemeasurable]
  change _ = ((Freezing1.Forward.treeLaw (Freezing2.companionSchedule x) n).bind
    (Freezing2.TreeSampling.forwardKernel k)).map _
  rw [Measure.map_bind measurable_from_top.aemeasurable
    (Freezing2.TreeSampling.measurable_forwardDistanceMatrix α n k).aemeasurable]
  congr 1
  funext s
  rw [Freezing2.TreeSampling.forwardKernel,
    Measure.map_map (Freezing2.TreeSampling.measurable_forwardDistanceMatrix α n k)
      measurable_prodMk_left]
  rfl

/-- The branch length vanishes at the root. -/
theorem branchLength_zero (f : ℝ → ℝ) : branchLength f 0 = 0 := by
  rw [branchLength, Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
    integral_zero_measure]

/-- On `[0, 1]`, the interface branch length is the library primitive of `1/f`. -/
theorem branchLength_eq_profilePrimitive (f : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    branchLength f t = Freezing2.profilePrimitive (fun s ↦ 1 / f s) t :=
  (Freezing2.profilePrimitive_reciprocal_eq f ht.1 ht.2).symm

/-- The interface star limit is the library one. -/
theorem starLimitLaw_eq {f : ℝ → ℝ} (hL1 : Integrable (fun t ↦ 1 / f t) profileMeasure)
    (k : ℕ) :
    starLimitLaw f k =
      ((Freezing2.iidSourceBranchLimit f k).map Freezing2.sourceStarMatrixMap :
        Measure (Fin (k + 1) → Fin (k + 1) → ℝ)) := by
  set g := Freezing2.profilePrimitive (fun s ↦ 1 / f s) with hg
  have hgc : Continuous g := Freezing2.continuous_profilePrimitive hL1
  have hmap : profileMeasure.map (Freezing2.sourceBranchPrimitive f) = profileMeasure.map g := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact branchLength_eq_profilePrimitive f ht
  rw [ProbabilityMeasure.toMeasure_map, Freezing2.iidSourceBranchLimit,
    ProbabilityMeasure.toMeasure_pi]
  simp only [ProbabilityMeasure.toMeasure_map]
  change _ = (Measure.pi fun _ : Fin k ↦ profileMeasure.map (Freezing2.sourceBranchPrimitive f)).map _
  rw [hmap, ← Measure.pi_map_pi (fun _ ↦ hgc.measurable.aemeasurable),
    Measure.map_map (Freezing2.continuous_sourceStarMatrixMap k).measurable
      (show Measurable fun (U : Fin k → ℝ) (i : Fin k) ↦ g (U i) from
        (continuous_pi fun i ↦ hgc.comp (continuous_apply i)).measurable),
    starLimitLaw]
  apply Measure.map_congr
  have hall : ∀ᵐ U ∂(Measure.pi fun _ : Fin k ↦ profileMeasure), ∀ i, U i ∈ Icc (0 : ℝ) 1 := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k ↦ profileMeasure) (i := i)).eventually
      (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hall] with U hU
  funext i j
  have hb : ∀ i : Fin (k + 1),
      branchLength f ((Fin.cases 0 U : Fin (k + 1) → ℝ) i) =
        Freezing2.sourceBranchCoordinate (fun l ↦ g (U l)) i := by
    intro i
    induction i using Fin.cases with
    | zero => simp [branchLength_zero]
    | succ l =>
      simp only [Fin.cases_succ, Freezing2.sourceBranchCoordinate_succ]
      exact branchLength_eq_profilePrimitive f (hU l)
  simp only [Function.comp_apply, Freezing2.sourceStarMatrixMap_eq_starDistance,
    Freezing2.Audit.starDistance, hb]

end FreezingStatements.Bridge
