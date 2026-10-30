module

public import Freezing2.Probability.TrackedRootCorrespondence
public import Freezing2.Probability.TrackedClusterExpectation
public import Freezing2.Probability.CoalescenceHistory

/-!
# Isolation probabilities from actual backward transition integrals

The value function starts from the literal isolation indicator and iterates the
actual reverse kernels. Its root-correspondence symmetry is derived from those
kernels. Two currently isolated marked components may be exchanged irrespective
of their untracked tree shapes; future birth labels must remain fixed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal

namespace Freezing2.TrackedClusters

open Freezing1 ForestCoalescence ReverseHistory ReverseCoalescence

/-- Backward evaluation of the actual isolation event, starting at source
phase `t+m` and ending at phase `t`. -/
noncomputable def isolationValue (x : SignSequence) (A : Finset (ℕ ⊕ ℕ)) (t : ℕ) :
    ℕ → Reverse.Forest → (ℕ ⊕ ℕ) → ℝ
  | 0, F, v => if Alone F A v then 1 else 0
  | m + 1, F, v => ∫ G, isolationValue x A t m G v ∂Reverse.transitionLaw x (t + m) F

theorem isolationValue_bounds (x : SignSequence) (A : Finset (ℕ ⊕ ℕ)) (t m : ℕ)
    (F : Reverse.Forest) (v : ℕ ⊕ ℕ) :
    0 ≤ isolationValue x A t m F v ∧ isolationValue x A t m F v ≤ 1 := by
  induction m generalizing F with
  | zero => simp only [isolationValue]; split_ifs <;> norm_num
  | succ m ih =>
    have hi : Integrable (fun G ↦ isolationValue x A t m G v)
        (Reverse.transitionLaw x (t + m) F) := by
      apply Integrable.mono' (integrable_const (1 : ℝ)) measurable_from_top.aestronglyMeasurable
      exact Eventually.of_forall fun G ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (ih G).1]
        exact (ih G).2
    constructor
    · exact integral_nonneg fun G ↦ (ih G).1
    · have h := integral_mono hi (integrable_const (1 : ℝ)) (fun G ↦ (ih G).2)
      simpa only [integral_const, probReal_univ, one_smul, isolationValue] using h

theorem integrable_isolationValue (x : SignSequence) (A : Finset (ℕ ⊕ ℕ)) (t m : ℕ)
    (v : ℕ ⊕ ℕ) (μ : Measure Reverse.Forest) [IsFiniteMeasure μ] :
    Integrable (fun F ↦ isolationValue x A t m F v) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) measurable_from_top.aestronglyMeasurable
  exact Eventually.of_forall fun F ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (isolationValue_bounds x A t m F v).1]
    exact (isolationValue_bounds x A t m F v).2

/-- A component which has met another marked vertex cannot become alone again. -/
theorem Alone.of_coarsens {V : Type*} [DecidableEq V] {F G : RootedForest V}
    {A : Finset V} {v : V} (hFG : Coarsens F G) (hG : Alone G A v) : Alone F A v := by
  intro w hw hvF hwF hroot
  exact hG w hw (hFG.1 hvF) (hFG.1 hwF) (hFG.2 v hvF w hwF hroot)

theorem isolationValue_eq_zero_of_not_alone (x : SignSequence)
    (A : Finset (ℕ ⊕ ℕ)) (t m : ℕ) (F : Reverse.Forest) (v : ℕ ⊕ ℕ)
    (hF : ¬Alone F A v) : isolationValue x A t m F v = 0 := by
  induction m generalizing F with
  | zero => exact ite_eq_right hF
  | succ m ih =>
    unfold isolationValue
    have heq : (fun G ↦ isolationValue x A t m G v) =ᵐ[Reverse.transitionLaw x (t + m) F]
        fun _ ↦ (0 : ℝ) := by
      filter_upwards [transitionLaw_ae_coarsens x (t + m) F] with G hFG
      exact ih G (fun hG ↦ hF (hG.of_coarsens hFG))
    rw [integral_congr_ae heq, integral_zero]

/-- Root correspondence gives future isolation symmetry by iterating the
actual transition integrals. All intervening birth labels are fixed. -/
theorem isolationValue_congr {x : SignSequence} {A : Finset (ℕ ⊕ ℕ)}
    {σ e : Equiv.Perm (ℕ ⊕ ℕ)} {t m : ℕ} {F G : Reverse.Forest}
    (h : RootCorrespondence A σ e F G) (hA : A.image σ = A)
    (hσ : ∀ j < m, σ (.inr (t + j)) = .inr (t + j))
    (he : ∀ j < m, e (.inr (t + j)) = .inr (t + j))
    {v : ℕ ⊕ ℕ} (hv : v ∈ A) :
    isolationValue x A t m F v = isolationValue x A t m G (σ v) := by
  induction m generalizing F G with
  | zero => simp only [isolationValue, h.alone_iff hA hv]
  | succ m ih =>
    simp only [isolationValue]
    apply h.integral_transitionLaw_eq x (t + m) (hσ m (Nat.lt_succ_self m))
      (he m (Nat.lt_succ_self m))
    intro F' G' hFG
    exact ih hFG (fun j hj ↦ hσ j (Nat.lt_succ_of_lt hj))
      (fun j hj ↦ he j (Nat.lt_succ_of_lt hj))

/-- A future freezing label is absent from every valid current forest. -/
theorem future_freezing_label_not_mem {x : SignSequence} {n b i : ℕ}
    {F : Reverse.Forest} (hF : Reverse.ValidAt x n b F) (hi : i < b) :
    Sum.inr i ∉ F.vertices := by
  rw [hF.vertices_eq]
  intro hmem
  have hbi := (Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hmem)).2.1
  omega

/-- Two present singleton marked components have equal future isolation
probabilities. This conclusion is proved without identifying their tree shapes. -/
theorem isolationValue_swap_of_alone {x : SignSequence} {n t m : ℕ}
    {F : Reverse.Forest} (hF : Reverse.ValidAt x n (t + m) F)
    {A : Finset (ℕ ⊕ ℕ)} {u v : ℕ ⊕ ℕ} (huA : u ∈ A) (hvA : v ∈ A)
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices)
    (huAl : Alone F A u) (hvAl : Alone F A v) :
    isolationValue x A t m F u = isolationValue x A t m F v := by
  have h := isolationValue_congr (x := x)
    (rootCorrespondence_swap_of_alone F hu hv huAl hvAl)
    (image_swap_eq_of_mem A huA hvA) (t := t) (m := m)
    (fun j hj ↦ ?_) (fun j hj ↦ ?_) huA
  · simpa only [Equiv.swap_apply_left] using h
  · have hfresh := future_freezing_label_not_mem hF (show t + j < t + m by omega)
    exact Equiv.swap_apply_of_ne_of_ne
      (fun heq ↦ hfresh (heq ▸ hu)) (fun heq ↦ hfresh (heq ▸ hv))
  · have hfresh := future_freezing_label_not_mem hF (show t + j < t + m by omega)
    exact Equiv.swap_apply_of_ne_of_ne
      (fun heq ↦ hfresh (heq ▸ F.root_mem u hu))
      (fun heq ↦ hfresh (heq ▸ F.root_mem v hv))

/-- If the younger component is currently alone, the older component's
future isolation probability is no larger: either both are alone and symmetry
applies, or the older component has already irreversibly merged. -/
theorem isolationValue_le_of_alone {x : SignSequence} {n t m : ℕ}
    {F : Reverse.Forest} (hF : Reverse.ValidAt x n (t + m) F)
    {A : Finset (ℕ ⊕ ℕ)} {u v : ℕ ⊕ ℕ} (huA : u ∈ A) (hvA : v ∈ A)
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (hvAl : Alone F A v) :
    isolationValue x A t m F u ≤ isolationValue x A t m F v := by
  by_cases huAl : Alone F A u
  · exact (isolationValue_swap_of_alone hF huA hvA hu hv huAl hvAl).le
  · rw [isolationValue_eq_zero_of_not_alone x A t m F u huAl]
    exact (isolationValue_bounds x A t m F v).1

/-- Generic bounded-observable bind integration for the actual reverse kernel. -/
theorem integral_bind_bounded (x : SignSequence) (i : ℕ)
    (μ : Measure Reverse.Forest) [IsProbabilityMeasure μ] (φ : Reverse.Forest → ℝ)
    (hφ : ∀ F, |φ F| ≤ 1) :
    (∫ G, φ G ∂μ.bind (Reverse.transitionLaw x i)) =
      ∫ F, ∫ G, φ G ∂Reverse.transitionLaw x i F ∂μ := by
  let κ : Kernel Reverse.Forest Reverse.Forest := ⟨Reverse.transitionLaw x i, measurable_from_top⟩
  have : IsProbabilityMeasure (μ.bind (Reverse.transitionLaw x i)) :=
    isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Eventually.of_forall fun F ↦ Reverse.transitionLaw_probability x i F)
  have hi : Integrable φ (μ.bind (Reverse.transitionLaw x i)) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) measurable_from_top.aestronglyMeasurable
    exact Eventually.of_forall fun F ↦ by simpa only [Real.norm_eq_abs] using hφ F
  have h := Kernel.integral_comp (κ := Kernel.const Unit μ) (η := κ) (a := ())
    (f := φ) (by simpa only [Kernel.comp_apply, Kernel.const_apply, κ, Kernel.coe_mk] using hi)
  simpa only [Kernel.comp_apply, Kernel.const_apply, κ, Kernel.coe_mk] using h

/-- The backward value integrates to the literal isolation probability under
the already constructed reverse marginal at the final phase. -/
theorem integral_isolationValue_lawAfter (x : SignSequence) {n t m : ℕ}
    (htm : t + m ≤ n) (A : Finset (ℕ ⊕ ℕ)) (v : ℕ ⊕ ℕ) :
    (∫ F, isolationValue x A t m F v ∂Reverse.lawAfter x n (n - (t + m))) =
      (Reverse.lawAfter x n (n - t)).real {F | Alone F A v} := by
  induction m with
  | zero =>
    simp only [Nat.add_zero, isolationValue]
    change (∫ F, ({F : Reverse.Forest | Alone F A v}).indicator (fun _ ↦ (1 : ℝ)) F
      ∂Reverse.lawAfter x n (n - t)) = _
    exact integral_indicator_one (by trivial)
  | succ m ih =>
    have hk : n - (t + (m + 1)) < n := by omega
    have he : n - (t + m) = n - (t + (m + 1)) + 1 := by omega
    have hphase : n - (n - (t + (m + 1)) + 1) = t + m := by omega
    have hnext : Reverse.lawAfter x n (n - (t + m)) =
        (Reverse.lawAfter x n (n - (t + (m + 1)))).bind (Reverse.transitionLaw x (t + m)) := by
      rw [he, Reverse.lawAfter, ite_eq_left hk, hphase]
    simp only [isolationValue]
    rw [← integral_bind_bounded x (t + m) _ _ (fun F ↦ by
      rw [abs_of_nonneg (isolationValue_bounds x A t m F v).1]
      exact (isolationValue_bounds x A t m F v).2), ← hnext]
    exact ih (by omega)

/-- At its actual birth phase a legal marked vertex is a singleton relative
to every fixed legal marked set, including vertices not born yet. -/
theorem lawAfter_alone_at_birth {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {A : Finset (ℕ ⊕ ℕ)}
    (hA : A ⊆ Freezing1.vertexLabels x n) {v : ℕ ⊕ ℕ}
    (hv : v ∈ Freezing1.vertexLabels x n) :
    ∀ᵐ F ∂Reverse.lawAfter x n (n - Freezing1.birthTime n v), Alone F A v := by
  have hdist : ∀ᵐ ω ∂jointLaw x n, ∀ w ∈ A, v ≠ w →
      ¬connectedAt n v w (commonBirth n v w) ω := by
    apply ae_all_iff.mpr
    intro w
    by_cases hw : w ∈ A
    · by_cases hne : v ≠ w
      · exact (jointLaw_distinct_at_commonBirth hn hv (hA hw) hne).mono fun _ h _ _ ↦ h
      · exact Eventually.of_forall fun _ _ h ↦ False.elim (hne h)
    · exact Eventually.of_forall fun _ h _ ↦ False.elim (hw h)
  rw [← jointLaw_map_eval]
  apply (ae_map_iff (μ := jointLaw x n)
    (f := fun ω : History ↦ ω (n - Freezing1.birthTime n v))
    (measurable_pi_apply _).aemeasurable
    (p := fun F : Reverse.Forest ↦ Alone F A v) (by trivial)).mpr
  filter_upwards [hdist, jointLaw_forestAt_valid x n hn] with ω hd hvalid
  intro w hw hvF hwF hroot
  by_contra hne
  have hb : Freezing1.birthTime n v ≤ n := birthTime_le_horizon hv
  have hF := hvalid (Freezing1.birthTime n v) hb
  have hwphase : w ∈ Reverse.phaseLabels x n (Freezing1.birthTime n v) := by
    rw [← hF.vertices_eq]
    exact hwF
  have hbw := (Reverse.mem_phaseLabels_iff_birthTime hb (hA hw)).mp hwphase
  apply hd w hw (Ne.symm hne)
  simpa only [connectedAt, commonBirth, min_eq_left hbw, forestAt] using hroot

/-- The oldest marked vertex is no more likely to remain isolated than a
specified younger marked vertex. The comparison is obtained at the younger
vertex's actual birth and then propagated through the actual kernels. -/
theorem isolation_probability_le_of_birth_order {x : SignSequence} {n t : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {A : Finset (ℕ ⊕ ℕ)}
    (hA : A ⊆ Freezing1.vertexLabels x n) {u v : ℕ ⊕ ℕ}
    (huA : u ∈ A) (hvA : v ∈ A)
    (hb : Freezing1.birthTime n v ≤ Freezing1.birthTime n u)
    (ht : t ≤ Freezing1.birthTime n v) :
    (Reverse.lawAfter x n (n - t)).real {F | Alone F A u} ≤
      (Reverse.lawAfter x n (n - t)).real {F | Alone F A v} := by
  let b := Freezing1.birthTime n v
  have hbn : b ≤ n := birthTime_le_horizon (hA hvA)
  have htm : t + (b - t) = b := by dsimp [b]; omega
  have hpoint : (fun F ↦ isolationValue x A t (b - t) F u)
      ≤ᵐ[Reverse.lawAfter x n (n - b)] fun F ↦ isolationValue x A t (b - t) F v := by
    filter_upwards [Reverse.lawAfter_valid x n (n - b) hn (Nat.sub_le _ _),
      lawAfter_alone_at_birth hn hA (hA hvA)] with F hF hvAl
    have hFb : Reverse.ValidAt x n b F := by
      simpa only [Nat.sub_sub_self hbn] using hF
    have hu : u ∈ F.vertices := by
      rw [hFb.vertices_eq]
      exact (Reverse.mem_phaseLabels_iff_birthTime hbn (hA huA)).mpr hb
    have hv : v ∈ F.vertices := by
      rw [hFb.vertices_eq]
      exact (Reverse.mem_phaseLabels_iff_birthTime hbn (hA hvA)).mpr le_rfl
    apply isolationValue_le_of_alone (by simpa only [htm] using hFb) huA hvA hu hv hvAl
  have h := integral_mono_ae (integrable_isolationValue x A t (b - t) u _)
    (integrable_isolationValue x A t (b - t) v _) hpoint
  have hu := integral_isolationValue_lawAfter x (show t + (b - t) ≤ n by omega) A u
  have hv := integral_isolationValue_lawAfter x (show t + (b - t) ≤ n by omega) A v
  rw [htm] at hu hv
  rwa [hu, hv] at h

end Freezing2.TrackedClusters
