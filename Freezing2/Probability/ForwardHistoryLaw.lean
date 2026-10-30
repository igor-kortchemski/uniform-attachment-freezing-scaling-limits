module

public import Freezing2.Companion.ForwardLaw
public import Freezing2.Companion.HistoryProbability

/-!
# Actual forward choice histories

The forward construction is lifted to finite lists of its uniform active-vertex
choices, written most recent first. Projecting a history to its terminal state
gives exactly `Forward.treeLaw`. This is a probability-law dependency of the
unique-history argument for N01, not an assertion of forward/reverse equality.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal

namespace Freezing2.ForwardHistory

abbrev History := List ℕ

instance : MeasurableSpace History := ⊤
instance : DiscreteMeasurableSpace History := ⟨fun _ ↦ trivial⟩

/-- Run the actual forward transitions using the recorded choices. -/
def state (x : Freezing1.SignSequence) : History → Freezing1.Forward.State
  | [] => Freezing1.Forward.initial
  | v :: h => Freezing1.Forward.step (state x h) (h.length + 1) (x (h.length + 1)) v

theorem state_valid (x : Freezing1.SignSequence) (h : History) :
    Freezing1.Forward.ValidAt h.length (state x h) := by
  induction h with
  | nil => exact Freezing1.Forward.initial_valid
  | cons v h ih => exact ih.step _ _

/-- At an absorbing state the placeholder choice is zero; the actual forward
transition leaves that state unchanged. Before extinction this branch is absent. -/
noncomputable def choiceLaw (s : Freezing1.Forward.State) : Measure ℕ :=
  if s.active.Nonempty then Measure.uniformOfFinset s.active else Measure.dirac 0

instance choiceLaw_probability (s : Freezing1.Forward.State) :
    IsProbabilityMeasure (choiceLaw s) := by
  unfold choiceLaw
  split_ifs with h
  · exact Freezing1.Forward.uniform_active_probability s h
  · infer_instance

theorem choiceLaw_apply_singleton_of_mem {s : Freezing1.Forward.State} {v : ℕ}
    (hv : v ∈ s.active) : choiceLaw s {v} = (s.active.card : ℝ≥0∞)⁻¹ := by
  rw [choiceLaw, ite_eq_left ⟨v, hv⟩]
  exact Measure.uniformOfFinset_apply_singleton_of_mem hv

/-- The choice law projects to the exact existing forward transition kernel. -/
theorem map_choiceLaw_step (s : Freezing1.Forward.State) (t : ℕ) (sign : Bool) :
    (choiceLaw s).map (Freezing1.Forward.step s t sign) =
      Freezing1.Forward.transitionLaw s t sign := by
  by_cases h : s.active.Nonempty
  · simp only [choiceLaw, Freezing1.Forward.transitionLaw, h, ite_true]
  · have he : s.active = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [choiceLaw, Freezing1.Forward.transitionLaw, h, ite_false]
    rw [Measure.map_dirac' (measurable_from_top)]
    simp only [Freezing1.Forward.step, he, Finset.notMem_empty, ite_false]

/-- Extend the complete history by one genuinely sampled active choice. -/
noncomputable def stepLaw (x : Freezing1.SignSequence) (h : History) : Measure History :=
  (choiceLaw (state x h)).map (fun v ↦ (v :: h : History))

instance stepLaw_probability (x : Freezing1.SignSequence) (h : History) :
    IsProbabilityMeasure (stepLaw x h) := by
  unfold stepLaw
  exact Measure.isProbabilityMeasure_map_iff (measurable_from_top.aemeasurable) |>.mpr inferInstance

theorem stepLaw_length (x : Freezing1.SignSequence) (h : History) :
    ∀ᵐ h' ∂stepLaw x h, h'.length = h.length + 1 := by
  rw [stepLaw, ae_map_iff (measurable_from_top.aemeasurable) (by trivial)]
  exact Eventually.of_forall fun _ ↦ rfl

theorem map_stepLaw_state (x : Freezing1.SignSequence) (h : History) :
    (stepLaw x h).map (state x) =
      Freezing1.Forward.transitionLaw (state x h) (h.length + 1) (x (h.length + 1)) := by
  rw [stepLaw, Measure.map_map measurable_from_top measurable_from_top]
  exact map_choiceLaw_step _ _ _

/-- The actual law of all choices through a finite horizon. -/
noncomputable def law (x : Freezing1.SignSequence) : ℕ → Measure History
  | 0 => Measure.dirac ([] : History)
  | n + 1 => (law x n).bind (stepLaw x)

instance law_probability (x : Freezing1.SignSequence) (n : ℕ) :
    IsProbabilityMeasure (law x n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac ([] : History)); infer_instance
  | succ n ih =>
    exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Eventually.of_forall fun h ↦ stepLaw_probability x h)

theorem law_length (x : Freezing1.SignSequence) (n : ℕ) :
    ∀ᵐ h ∂law x n, h.length = n := by
  induction n with
  | zero => simp [law]
  | succ n ih =>
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [law, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _h, (1 : ℝ≥0∞) ∂law x n := by
        apply lintegral_congr_ae
        filter_upwards [ih] with h hh
        apply (ae_iff_prob_eq_one measurable_from_top).mp
        simpa only [hh] using stepLaw_length x h
      _ = 1 := by simp

/-- The history construction is a lift of the actual forward tree law, not
an independently postulated history distribution. -/
theorem map_law_state (x : Freezing1.SignSequence) (n : ℕ) :
    (law x n).map (state x) = Freezing1.Forward.treeLaw x n := by
  induction n with
  | zero => exact Measure.map_dirac' measurable_from_top _
  | succ n ih =>
    rw [law, Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    calc
      _ = (law x n).bind (fun h ↦
          Freezing1.Forward.transitionLaw (state x h) (n + 1) (x (n + 1))) := by
        apply Measure.ext
        intro A hA
        rw [Measure.bind_apply hA measurable_from_top.aemeasurable,
          Measure.bind_apply hA measurable_from_top.aemeasurable]
        apply lintegral_congr_ae
        filter_upwards [law_length x n] with h hh
        rw [map_stepLaw_state, hh]
      _ = ((law x n).map (state x)).bind
          (fun s ↦ Freezing1.Forward.transitionLaw s (n + 1) (x (n + 1))) :=
        (Measure.bind_map (m := law x n) (f := state x)
          (g := fun s : Freezing1.Forward.State ↦
            Freezing1.Forward.transitionLaw s (n + 1) (x (n + 1)))
          measurable_from_top.aemeasurable measurable_from_top.aemeasurable).symm
      _ = _ := by rw [ih]; rfl

/-- A legal history records an active choice at every performed step. -/
def Legal (x : Freezing1.SignSequence) : History → Prop
  | [] => True
  | v :: h => Legal x h ∧ v ∈ (state x h).active

/-- The exact product of the genuine uniform-choice factors along a history. -/
noncomputable def weight (x : Freezing1.SignSequence) : History → ℝ≥0∞
  | [] => 1
  | _v :: h => ((state x h).active.card : ℝ≥0∞)⁻¹ * weight x h

theorem stepLaw_apply_cons (x : Freezing1.SignSequence) (h' h : History) (v : ℕ) :
    stepLaw x h' {(v :: h : History)} =
      if h' = h then choiceLaw (state x h) {v} else 0 := by
  rw [stepLaw, Measure.map_apply measurable_from_top (by trivial)]
  by_cases hh : h' = h
  · subst h'
    have he : (fun w : ℕ ↦ (w :: h : History)) ⁻¹' {(v :: h : History)} = {v} := by
      ext w
      simp
    rw [he, ite_eq_left rfl]
  · have he : (fun w : ℕ ↦ (w :: h' : History)) ⁻¹' {(v :: h : History)} = ∅ := by
      ext w
      simp [hh]
    rw [he, measure_empty, ite_eq_right hh]

/-- Prefix uniqueness is already explicit at the choice-list level. -/
theorem law_apply_cons (x : Freezing1.SignSequence) (n : ℕ) (h : History) (v : ℕ) :
    law x (n + 1) {(v :: h : History)} = choiceLaw (state x h) {v} * law x n {h} := by
  rw [law, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  calc
    _ = ∫⁻ h', ({h} : Set History).indicator (fun _ ↦ choiceLaw (state x h) {v}) h'
        ∂law x n := by
      apply lintegral_congr
      intro h'
      rw [stepLaw_apply_cons]
      simp only [Set.indicator, Set.mem_singleton_iff]
    _ = _ := lintegral_indicator_const (measurableSet_singleton h) _

/-- The probability of a legal history is its product of actual transition
probabilities. This does not yet identify distinct terminal states with histories. -/
theorem law_singleton_of_legal (x : Freezing1.SignSequence) {h : History}
    (hh : Legal x h) : law x h.length {h} = weight x h := by
  induction h with
  | nil => simp [law, weight]
  | cons v h ih =>
    rw [List.length_cons, law_apply_cons, choiceLaw_apply_singleton_of_mem hh.2, ih hh.1]
    rfl

theorem weight_pos_of_legal (x : Freezing1.SignSequence) {h : History}
    (hh : Legal x h) : 0 < weight x h := by
  induction h with
  | nil => simp [weight]
  | cons v h ih =>
    exact ENNReal.mul_pos (by simp) (ne_of_gt (ih hh.1))

/-- Counts for every legal fixed history follow from its positive mass under
the actual process and the already proved almost-sure forward counts. -/
theorem state_counts_of_legal (x : Freezing1.SignSequence) {h : History}
    (hh : Legal x h) (hn : (h.length : ℕ∞) ≤ Freezing1.extinctionTime x) :
    ((state x h).active.card : ℤ) = Freezing1.activeCount x h.length ∧
      (state x h).vertices.card = Freezing1.plusCount x h.length + 1 := by
  have hae : ∀ᵐ h' ∂law x h.length,
      ((state x h').active.card : ℤ) = Freezing1.activeCount x h.length ∧
        (state x h').vertices.card = Freezing1.plusCount x h.length + 1 := by
    have hc := Freezing1.Forward.treeLaw_counts x h.length hn
    rw [← map_law_state] at hc
    exact ae_of_ae_map (f := state x) measurable_from_top.aemeasurable hc
  by_contra hnot
  have hzero : law x h.length {h} = 0 :=
    measure_mono_null (by simpa only [Set.singleton_subset_iff, Set.mem_ofPred_eq] using hnot)
      (ae_iff.mp hae)
  rw [law_singleton_of_legal x hh] at hzero
  exact (ne_of_gt (weight_pos_of_legal x hh)) hzero

/-- The source history product is now the probability of an actual fixed
history, including the extinction endpoint. Terminal history uniqueness and
reverse active-label fibre counting remain separate obligations. -/
theorem law_real_singleton_of_legal (x : Freezing1.SignSequence) {h : History}
    (hh : Legal x h) (hn : (h.length : ℕ∞) ≤ Freezing1.extinctionTime x) :
    (law x h.length).real {h} = Freezing1.forwardHistoryWeight x h.length := by
  induction h with
  | nil => simp [law]
  | cons v h ih =>
    have hpre : (h.length : ℕ∞) ≤ Freezing1.extinctionTime x :=
      le_trans (by exact_mod_cast Nat.le_succ h.length) hn
    have hcount : ((state x h).active.card : ℝ) = (Freezing1.activeCount x h.length : ℝ) := by
      exact_mod_cast (state_counts_of_legal x hh.1 hpre).1
    change (law x (h.length + 1) {(v :: h : History)}).toReal = _
    rw [law_apply_cons, choiceLaw_apply_singleton_of_mem hh.2, ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_natCast, hcount]
    change _ * (law x h.length).real {h} = _
    rw [ih hh.1 hpre, List.length_cons, Freezing1.forwardHistoryWeight_succ]
    ring

/-- For a fixed valid predecessor, distinct legal choices give distinct next
states. This verifies the one-step uniqueness used by the source counting proof. -/
theorem step_injOn_active {n : ℕ} {s : Freezing1.Forward.State}
    (hs : Freezing1.Forward.ValidAt n s) (t : ℕ) (sign : Bool) :
    Set.InjOn (Freezing1.Forward.step s t sign) (s.active : Set ℕ) := by
  intro v hv w hw he
  change v ∈ s.active at hv
  change w ∈ s.active at hw
  cases sign with
  | true =>
    have hp := congrArg (fun s' : Freezing1.Forward.State ↦ s'.parent t) he
    simpa only [Freezing1.Forward.step, ite_eq_left hv, ite_eq_left hw, ite_true,
      Freezing1.Forward.attach, Function.update_self] using hp
  | false =>
    by_contra hne
    have hf := congrArg (fun s' : Freezing1.Forward.State ↦ s'.frozenAt v) he
    have hvnone := (hs.active_iff v (hs.active_subset hv)).mp hv
    simp only [Freezing1.Forward.step, ite_eq_left hv, ite_eq_left hw,
      Bool.false_eq_true, ite_false, Freezing1.Forward.freeze, Function.update_self,
      Function.update_of_ne hne, hvnone] at hf
    cases hf

end Freezing2.ForwardHistory
