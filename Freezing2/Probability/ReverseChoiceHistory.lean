module

public import Freezing2.Probability.ReverseStampedTransition
public import Freezing2.Companion.HistoryProbability

/-!
# The actual ordered-root choices of the stamped reverse process

Finite histories retain each sampled ordered root pair; freezing steps have one
deterministic placeholder. Their projection is exactly the stamped reverse law.
This provides the probability-law side of N01's reverse history counting proof.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Classical

namespace Freezing2.ReverseChoiceHistory

abbrev Forest := Freezing1.ReverseStamped.Forest
abbrev Choice := (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)
abbrev History := List Choice

instance : MeasurableSpace History := ⊤
instance : DiscreteMeasurableSpace History := ⟨fun _ ↦ trivial⟩

def noChoice : Choice := (Sum.inl 0, Sum.inl 0)

/-- The deterministic stamped transition driven by its ordered root choice. -/
def step (x : Freezing1.SignSequence) (i : ℕ) (F : Forest) (p : Choice) : Forest :=
  if x (i + 1) then Freezing1.ReverseStamped.joinChoice F (i + 1) p
  else Freezing1.ReverseStamped.insertLabel F i

/-- The latest reverse choice is first in the list. Only lengths at most `n`
are used in the source process. -/
def state (x : Freezing1.SignSequence) (n : ℕ) : History → Forest
  | [] => Freezing1.ReverseStamped.initial x n
  | p :: h => step x (n - (h.length + 1)) (state x n h) p

/-- Uniform root choices for a merge, and a deterministic placeholder when
there is no random choice. The too-few-roots branch matches the total kernel. -/
noncomputable def choiceLaw (F : Forest) (sign : Bool) : Measure Choice :=
  if sign ∧ 2 ≤ F.forest.roots.card then Freezing1.uniformRootPair F.forest.roots
  else Measure.dirac noChoice

instance choiceLaw_probability (F : Forest) (sign : Bool) :
    IsProbabilityMeasure (choiceLaw F sign) := by
  unfold choiceLaw
  split_ifs with h
  · exact Freezing1.uniformRootPair_isProbabilityMeasure _ h.2
  · infer_instance

/-- Recording the ordered pair leaves the exact reverse transition law unchanged. -/
theorem map_choiceLaw_step (x : Freezing1.SignSequence) (i : ℕ) (F : Forest) :
    (choiceLaw F (x (i + 1))).map (step x i F) =
      Freezing1.ReverseStamped.transitionLaw x i F := by
  cases hx : x (i + 1) with
  | false =>
    simp only [choiceLaw, hx, Bool.false_eq_true, false_and, ite_false,
      Freezing1.ReverseStamped.transitionLaw]
    rw [Measure.map_dirac' (measurable_of_countable _)]
    simp [step, hx]
  | true =>
    by_cases htwo : 2 ≤ F.forest.roots.card
    · simp only [choiceLaw, hx, true_and, htwo, ite_true,
        Freezing1.ReverseStamped.transitionLaw, Freezing1.ReverseStamped.joinLaw]
      congr 1
      funext p
      simp [step, hx]
    · simp only [choiceLaw, hx, true_and, htwo, ite_false,
        Freezing1.ReverseStamped.transitionLaw, ite_true, Freezing1.ReverseStamped.joinLaw]
      rw [Measure.map_dirac' (measurable_of_countable _)]
      simp [step, hx, Freezing1.ReverseStamped.joinChoice, noChoice]

noncomputable def stepLaw (x : Freezing1.SignSequence) (n : ℕ) (h : History) :
    Measure History :=
  (choiceLaw (state x n h) (x (n - (h.length + 1) + 1))).map (fun p ↦ p :: h)

instance stepLaw_probability (x : Freezing1.SignSequence) (n : ℕ) (h : History) :
    IsProbabilityMeasure (stepLaw x n h) := by
  unfold stepLaw
  exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable
    |>.mpr inferInstance

theorem map_stepLaw_state (x : Freezing1.SignSequence) (n : ℕ) (h : History) :
    (stepLaw x n h).map (state x n) =
      Freezing1.ReverseStamped.transitionLaw x (n - (h.length + 1)) (state x n h) := by
  rw [stepLaw, Measure.map_map measurable_from_top (measurable_of_countable _)]
  exact map_choiceLaw_step _ _ _

noncomputable def law (x : Freezing1.SignSequence) (n : ℕ) : ℕ → Measure History
  | 0 => Measure.dirac ([] : History)
  | k + 1 => (law x n k).bind (stepLaw x n)

instance law_probability (x : Freezing1.SignSequence) (n k : ℕ) :
    IsProbabilityMeasure (law x n k) := by
  induction k with
  | zero => change IsProbabilityMeasure (Measure.dirac ([] : History)); infer_instance
  | succ k ih =>
    exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Eventually.of_forall fun h ↦ stepLaw_probability x n h)

theorem law_length (x : Freezing1.SignSequence) (n k : ℕ) :
    ∀ᵐ h ∂law x n k, h.length = k := by
  induction k with
  | zero => simp [law]
  | succ k ih =>
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [law, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _h, (1 : ℝ≥0∞) ∂law x n k := by
        apply lintegral_congr_ae
        filter_upwards [ih] with h hh
        apply (ae_iff_prob_eq_one measurable_from_top).mp
        rw [stepLaw, ae_map_iff (measurable_of_countable _).aemeasurable (by trivial)]
        exact Eventually.of_forall fun _ ↦ by simp [hh]
      _ = 1 := by simp

/-- At every source phase this is a lift of the existing stamped reverse law. -/
theorem map_law_state (x : Freezing1.SignSequence) (n k : ℕ) (hk : k ≤ n) :
    (law x n k).map (state x n) = Freezing1.ReverseStamped.lawAfter x n k := by
  induction k with
  | zero => exact Measure.map_dirac' measurable_from_top _
  | succ k ih =>
    rw [law, Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    calc
      _ = (law x n k).bind (fun h ↦
          Freezing1.ReverseStamped.transitionLaw x (n - (k + 1)) (state x n h)) := by
        apply Measure.ext
        intro A hA
        rw [Measure.bind_apply hA measurable_from_top.aemeasurable,
          Measure.bind_apply hA measurable_from_top.aemeasurable]
        apply lintegral_congr_ae
        filter_upwards [law_length x n k] with h hh
        rw [map_stepLaw_state, hh]
      _ = ((law x n k).map (state x n)).bind
          (Freezing1.ReverseStamped.transitionLaw x (n - (k + 1))) :=
        (Measure.bind_map (m := law x n k) (f := state x n)
          (g := Freezing1.ReverseStamped.transitionLaw x (n - (k + 1)))
          measurable_from_top.aemeasurable measurable_from_top.aemeasurable).symm
      _ = _ := by
        rw [ih (by omega), Freezing1.ReverseStamped.lawAfter, ite_eq_left (by omega)]

/-- Schedule-compatible root-pair histories; freezing steps have no free choice. -/
def Legal (x : Freezing1.SignSequence) (n : ℕ) : History → Prop
  | [] => True
  | p :: h => Legal x n h ∧ h.length < n ∧
      if x (n - (h.length + 1) + 1) then
        p ∈ (state x n h).forest.roots.offDiag else p = noChoice

theorem Legal.length_le {x : Freezing1.SignSequence} {n : ℕ} {h : History}
    (hh : Legal x n h) : h.length ≤ n := by
  cases h with
  | nil => simp
  | cons p h => exact Nat.succ_le_of_lt hh.2.1

noncomputable def weight (x : Freezing1.SignSequence) (n : ℕ) : History → ℝ≥0∞
  | [] => 1
  | _p :: h =>
      (if x (n - (h.length + 1) + 1) then
        ((state x n h).forest.roots.offDiag.card : ℝ≥0∞)⁻¹ else 1) * weight x n h

theorem choiceLaw_apply_singleton {F : Forest} {sign : Bool} {p : Choice}
    (hp : if sign then p ∈ F.forest.roots.offDiag else p = noChoice) :
    choiceLaw F sign {p} = if sign then (F.forest.roots.offDiag.card : ℝ≥0∞)⁻¹ else 1 := by
  cases sign with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hp ⊢
    simp [choiceLaw, hp]
  | true =>
    simp only [ite_true] at hp ⊢
    have htwo : 2 ≤ F.forest.roots.card :=
      Finset.one_lt_card.mpr ⟨p.1, (Finset.mem_offDiag.mp hp).1,
        p.2, (Finset.mem_offDiag.mp hp).2.1, (Finset.mem_offDiag.mp hp).2.2⟩
    simp only [choiceLaw, true_and, htwo, ite_true,
      Freezing1.uniformRootPair]
    exact Measure.uniformOfFinset_apply_singleton_of_mem hp

theorem law_apply_cons (x : Freezing1.SignSequence) (n k : ℕ) (h : History) (p : Choice) :
    law x n (k + 1) {p :: h} =
      choiceLaw (state x n h) (x (n - (h.length + 1) + 1)) {p} * law x n k {h} := by
  rw [law, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  calc
    _ = ∫⁻ h', ({h} : Set History).indicator
        (fun _ ↦ choiceLaw (state x n h) (x (n - (h.length + 1) + 1)) {p}) h' ∂law x n k := by
      apply lintegral_congr
      intro h'
      rw [stepLaw, Measure.map_apply (measurable_of_countable _) (by trivial)]
      by_cases hh : h' = h
      · subst h'
        have he : (fun q : Choice ↦ q :: h) ⁻¹' {p :: h} = {p} := by ext q; simp
        simp [he]
      · have he : (fun q : Choice ↦ q :: h') ⁻¹' {p :: h} = ∅ := by ext q; simp [hh]
        simp [he, hh]
    _ = _ := lintegral_indicator_const (measurableSet_singleton h) _

theorem law_singleton_of_legal (x : Freezing1.SignSequence) (n : ℕ) {h : History}
    (hh : Legal x n h) : law x n h.length {h} = weight x n h := by
  induction h with
  | nil => simp [law, weight]
  | cons p h ih =>
    rw [List.length_cons, law_apply_cons, choiceLaw_apply_singleton hh.2.2, ih hh.1]
    rfl

theorem weight_pos_of_legal (x : Freezing1.SignSequence) (n : ℕ) {h : History}
    (hh : Legal x n h) : 0 < weight x n h := by
  induction h with
  | nil => simp [weight]
  | cons p h ih =>
    apply ENNReal.mul_pos _ (ne_of_gt (ih hh.1))
    split_ifs
    · exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
    · exact one_ne_zero

/-- Every fixed legal history inherits the actual reverse structural and
schedule invariants from its positive atom under the exact lifted law. -/
theorem state_valid_of_legal (x : Freezing1.SignSequence) (n : ℕ) {h : History}
    (hh : Legal x n h) (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    Freezing1.Reverse.ValidAt x n (n - h.length) (state x n h).forest ∧
      Freezing1.ReverseStamped.TimesValidAt x n (n - h.length) (state x n h) := by
  have hae : ∀ᵐ F ∂Freezing1.ReverseStamped.lawAfter x n h.length,
      Freezing1.Reverse.ValidAt x n (n - h.length) F.forest ∧
        Freezing1.ReverseStamped.TimesValidAt x n (n - h.length) F :=
    (Freezing1.ReverseStamped.lawAfter_forest_valid x n h.length hn hh.length_le).and
      (Freezing1.ReverseStamped.lawAfter_times_valid x n h.length hn hh.length_le)
  rw [← map_law_state x n h.length hh.length_le] at hae
  have ha := ae_of_ae_map (f := state x n) measurable_from_top.aemeasurable hae
  by_contra hnot
  have hz : law x n h.length {h} = 0 :=
    measure_mono_null (by simpa only [Set.singleton_subset_iff, Set.mem_ofPred_eq] using hnot)
      (ae_iff.mp ha)
  rw [law_singleton_of_legal x n hh] at hz
  exact (ne_of_gt (weight_pos_of_legal x n hh)) hz

end Freezing2.ReverseChoiceHistory
