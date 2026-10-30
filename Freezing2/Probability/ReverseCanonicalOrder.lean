module

public import Freezing2.Probability.ReverseChoiceHistory

/-!
# Canonical birth-time order in the actual stamped reverse forest

Incoming timestamps are the canonical forward birth identifiers. A parent's
identifier precedes its child's identifier, and a vertex born before its
freezing step has an identifier at most its zero-based frozen label. These
facts are proved directly through the stamped reverse transitions.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Classical

namespace Freezing2.ReverseStamped

/-- The order conditions used to reconstruct the canonical forward tree.
`TimesValidAt.root_zero` identifies the nonzero premise with being a nonroot. -/
structure CanonicalOrder (F : Forest) : Prop where
  parent_lt : ∀ v ∈ F.forest.vertices, F.edgeTime v ≠ 0 →
    F.edgeTime (F.forest.parent v) < F.edgeTime v
  frozen_le : ∀ j, Sum.inr j ∈ F.forest.vertices → F.edgeTime (Sum.inr j) ≤ j
  frozen_parent_le : ∀ v ∈ F.forest.vertices, ∀ j,
    F.forest.parent v = Sum.inr j → F.edgeTime v ≤ j

theorem CanonicalOrder.parent_lt_of_not_root {x : Freezing1.SignSequence}
    {n i : ℕ} {F : Forest} (hO : CanonicalOrder F)
    (hT : Freezing1.ReverseStamped.TimesValidAt x n i F)
    {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices) (hr : v ∉ F.forest.roots) :
    F.edgeTime (F.forest.parent v) < F.edgeTime v :=
  hO.parent_lt v hv (fun hz ↦ hr ((hT.root_zero v hv).mp hz))

theorem initial_canonicalOrder (x : Freezing1.SignSequence) (n : ℕ) :
    CanonicalOrder (Freezing1.ReverseStamped.initial x n) := by
  constructor
  · intro v _ hnz
    simp [Freezing1.ReverseStamped.initial] at hnz
  · intro j _
    simp [Freezing1.ReverseStamped.initial]
  · intro v _ j _
    simp [Freezing1.ReverseStamped.initial]

/-- At a reverse merge the new edge has the smallest positive timestamp.
It can change the timestamp of an old parent only to that smaller value. -/
theorem CanonicalOrder.joinChoice {x : Freezing1.SignSequence} {n i : ℕ}
    {F : Forest} (hO : CanonicalOrder F)
    (hF : Freezing1.Reverse.ValidAt x n (i + 1) F.forest)
    (hT : Freezing1.ReverseStamped.TimesValidAt x n (i + 1) F)
    {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)} (hp : p ∈ F.forest.roots.offDiag) :
    CanonicalOrder (Freezing1.ReverseStamped.joinChoice F (i + 1) p) := by
  have ha := (Finset.mem_offDiag.mp hp).1
  have hab := (Finset.mem_offDiag.mp hp).2.2
  have haz : F.edgeTime p.1 = 0 :=
    (hT.root_zero p.1 (Freezing1.RootedForest.mem_roots.mp ha).1).mpr ha
  constructor
  · intro v hv hnz
    simp only [Freezing1.ReverseStamped.joinChoice, dite_eq_left hp] at hv hnz ⊢
    change v ∈ F.forest.vertices at hv
    change Function.update F.edgeTime p.2 (i + 1)
        (if v = p.2 then p.1 else F.forest.parent v) <
      Function.update F.edgeTime p.2 (i + 1) v
    by_cases hvb : v = p.2
    · subst v
      simp [hab, haz]
    · simp only [hvb, ite_false, Function.update_of_ne hvb] at hnz ⊢
      by_cases hpb : F.forest.parent v = p.2
      · rw [hpb, Function.update_self]
        exact (hT.range v hv hnz).1
      · rw [Function.update_of_ne hpb]
        exact hO.parent_lt v hv hnz
  · intro j hv
    simp only [Freezing1.ReverseStamped.joinChoice, dite_eq_left hp] at hv ⊢
    change Sum.inr j ∈ F.forest.vertices at hv
    by_cases hj : Sum.inr j = p.2
    · have hphase : i + 1 ≤ j := by
        rw [hF.vertices_eq] at hv
        simp only [Freezing1.Reverse.phaseLabels, Finset.inr_mem_disjSum,
          Finset.mem_filter, Finset.mem_range] at hv
        exact hv.2.1
      simpa [hj] using hphase
    · simpa only [Function.update_of_ne hj] using hO.frozen_le j hv
  · intro v hv j hpv
    simp only [Freezing1.ReverseStamped.joinChoice, dite_eq_left hp] at hv hpv ⊢
    change v ∈ F.forest.vertices at hv
    change (if v = p.2 then p.1 else F.forest.parent v) = Sum.inr j at hpv
    by_cases hvb : v = p.2
    · have haj : p.1 = Sum.inr j := by simpa [hvb] using hpv
      have hjmem : Sum.inr j ∈ Freezing1.Reverse.phaseLabels x n (i + 1) := by
        rw [← hF.vertices_eq, ← haj]
        exact (Freezing1.RootedForest.mem_roots.mp ha).1
      have hphase : i + 1 ≤ j := by
        simp only [Freezing1.Reverse.phaseLabels, Finset.inr_mem_disjSum,
          Finset.mem_filter, Finset.mem_range] at hjmem
        exact hjmem.2.1
      simpa [hvb] using hphase
    · simp only [hvb, ite_false] at hpv
      simpa only [Function.update_of_ne hvb] using hO.frozen_parent_le v hv j hpv

/-- A freezing step inserts a fresh zero-timestamp singleton; all old parent
relations and their timestamps keep their order. -/
theorem CanonicalOrder.insertLabel {F : Forest} (hO : CanonicalOrder F) (i : ℕ)
    (hfresh : Sum.inr i ∉ F.forest.vertices) :
    CanonicalOrder (Freezing1.ReverseStamped.insertLabel F i) := by
  constructor
  · intro v hv hnz
    simp only [Freezing1.ReverseStamped.insertLabel, dite_eq_right hfresh,
      Freezing1.RootedForest.adjoin_vertices] at hv hnz ⊢
    have hvi : v ≠ Sum.inr i := by intro he; simp [he] at hnz
    have hvold := (Finset.mem_insert.mp hv).resolve_left hvi
    have hpi : F.forest.parent v ≠ Sum.inr i :=
      fun he ↦ hfresh (he ▸ F.forest.parent_mem v hvold)
    simp only [Function.update_of_ne hvi] at hnz
    change Function.update F.edgeTime (Sum.inr i) 0
        (if v = Sum.inr i then Sum.inr i else F.forest.parent v) <
      Function.update F.edgeTime (Sum.inr i) 0 v
    simpa [hvi, hpi] using hO.parent_lt v hvold hnz
  · intro j hv
    simp only [Freezing1.ReverseStamped.insertLabel, dite_eq_right hfresh,
      Freezing1.RootedForest.adjoin_vertices] at hv ⊢
    by_cases hji : Sum.inr j = (Sum.inr i : ℕ ⊕ ℕ)
    · simp [hji]
    · simpa only [Function.update_of_ne hji] using
        hO.frozen_le j ((Finset.mem_insert.mp hv).resolve_left hji)
  · intro v hv j hpv
    simp only [Freezing1.ReverseStamped.insertLabel, dite_eq_right hfresh,
      Freezing1.RootedForest.adjoin_vertices] at hv hpv ⊢
    change (if v = Sum.inr i then Sum.inr i else F.forest.parent v) = Sum.inr j at hpv
    by_cases hvi : v = Sum.inr i
    · simp [hvi]
    · have hvold := (Finset.mem_insert.mp hv).resolve_left hvi
      simp only [hvi, ite_false] at hpv
      simpa only [Function.update_of_ne hvi] using hO.frozen_parent_le v hvold j hpv

/-- The actual stamped reverse transition preserves canonical order. -/
theorem transitionLaw_canonicalOrder {x : Freezing1.SignSequence} {n i : ℕ}
    {F : Forest} (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hi : i < n)
    (hF : Freezing1.Reverse.ValidAt x n (i + 1) F.forest)
    (hT : Freezing1.ReverseStamped.TimesValidAt x n (i + 1) F)
    (hO : CanonicalOrder F) :
    ∀ᵐ F' ∂Freezing1.ReverseStamped.transitionLaw x i F, CanonicalOrder F' := by
  cases hx : x (i + 1)
  · have hfresh : Sum.inr i ∉ F.forest.vertices := by
      rw [hF.vertices_eq]
      exact Freezing1.Reverse.fresh_freezing_label x n i
    simp only [Freezing1.ReverseStamped.transitionLaw, hx, Bool.false_eq_true, ite_false]
    exact (ae_dirac_iff (by trivial)).mpr (hO.insertLabel i hfresh)
  · have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ Freezing1.extinctionTime x :=
      le_trans (by exact_mod_cast Nat.succ_le_of_lt hi) hn
    have htwo : 2 ≤ F.forest.roots.card := by
      rw [hF.roots_card]
      exact Freezing1.two_le_activeCount_toNat_succ_of_attachment hiτ hx
    simp only [Freezing1.ReverseStamped.transitionLaw, hx, ite_true]
    exact Freezing1.ReverseStamped.joinLaw_ae F (i + 1) htwo CanonicalOrder
      (fun _ hp ↦ hO.joinChoice hF hT hp)

/-- Every actual reverse phase satisfies both canonical order conditions,
including horizons ending exactly at extinction. -/
theorem lawAfter_canonicalOrder (x : Freezing1.SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hk : k ≤ n) :
    ∀ᵐ F ∂Freezing1.ReverseStamped.lawAfter x n k, CanonicalOrder F := by
  induction k with
  | zero => simpa [Freezing1.ReverseStamped.lawAfter] using initial_canonicalOrder x n
  | succ k ih =>
    have hkn : k < n := by omega
    have hphase : n - k = n - (k + 1) + 1 := by omega
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [Freezing1.ReverseStamped.lawAfter, ite_eq_left hkn,
      Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _F, (1 : ℝ≥0∞) ∂Freezing1.ReverseStamped.lawAfter x n k := by
        apply lintegral_congr_ae
        filter_upwards [ih (by omega),
          Freezing1.ReverseStamped.lawAfter_forest_valid x n k hn (by omega),
          Freezing1.ReverseStamped.lawAfter_times_valid x n k hn (by omega)] with F hO hF hT
        rw [hphase] at hF hT
        exact (ae_iff_prob_eq_one measurable_from_top).mp
          (transitionLaw_canonicalOrder hn (by omega) hF hT hO)
      _ = 1 := by simp

theorem treeLaw_canonicalOrder (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    ∀ᵐ F ∂Freezing1.ReverseStamped.treeLaw x n, CanonicalOrder F :=
  lawAfter_canonicalOrder x n n hn le_rfl

/-- Every fixed legal root-choice history has the same proved order conditions;
this transfers the actual almost-sure invariant through its positive atom. -/
theorem state_canonicalOrder_of_legal (x : Freezing1.SignSequence) (n : ℕ)
    {h : ReverseChoiceHistory.History} (hh : ReverseChoiceHistory.Legal x n h)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    CanonicalOrder (ReverseChoiceHistory.state x n h) := by
  have hae := lawAfter_canonicalOrder x n h.length hn hh.length_le
  rw [← ReverseChoiceHistory.map_law_state x n h.length hh.length_le] at hae
  have ha := ae_of_ae_map (f := ReverseChoiceHistory.state x n)
    measurable_from_top.aemeasurable hae
  by_contra hnot
  have hz : ReverseChoiceHistory.law x n h.length {h} = 0 :=
    measure_mono_null (by simpa only [Set.singleton_subset_iff, Set.mem_ofPred_eq] using hnot)
      (ae_iff.mp ha)
  rw [ReverseChoiceHistory.law_singleton_of_legal x n hh] at hz
  exact (ne_of_gt (ReverseChoiceHistory.weight_pos_of_legal x n hh)) hz

end Freezing2.ReverseStamped
