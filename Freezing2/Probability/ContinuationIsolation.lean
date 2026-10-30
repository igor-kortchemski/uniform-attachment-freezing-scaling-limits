module

public import Freezing2.Probability.ReverseContinuation
public import Freezing2.Probability.OldestIsolation

/-!
# Oldest isolation from an arbitrary valid starting forest

The younger marked labels are not yet born at the starting phase. Each is
inserted as a fresh singleton by its actual freezing kernel. Root symmetry
and irreversible coalescence then yield the same oldest-isolation comparison
for every valid initial forest, without any conditional independence premise.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace Freezing2.ReverseContinuation

open Freezing1 Freezing2.TrackedClusters Freezing2.ForestCoalescence

theorem alone_insertLabel (F : Reverse.Forest) (i : ℕ) (A : Finset (ℕ ⊕ ℕ))
    (hfresh : Sum.inr i ∉ F.vertices) : Alone (Reverse.insertLabel F i) A (.inr i) := by
  intro w _ _ hw hroot
  have hvertices : (Reverse.insertLabel F i).vertices = insert (.inr i) F.vertices := by
    simp only [Reverse.insertLabel, dite_eq_right hfresh, RootedForest.adjoin_vertices]
  rw [hvertices] at hw
  rcases Finset.mem_insert.mp hw with hw | hw
  · exact hw
  · exact False.elim ((insertLabel_root_new_ne_old F i hfresh hw) hroot)

/-- A marked label born strictly after the continuation starts is alone at
its birth under the actual continuation law, whatever the initial tree shapes. -/
theorem law_alone_at_birth {x : SignSequence} {n s : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hs : s ≤ n) (hF : Reverse.ValidAt x n s F)
    (A : Finset (ℕ ⊕ ℕ)) {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n)
    (hb : Freezing1.birthTime n v < s) :
    ∀ᵐ G ∂law x s F (s - Freezing1.birthTime n v), Alone G A v := by
  cases v with
  | inl a => simp only [Freezing1.birthTime] at hb; omega
  | inr b =>
    have hb' : b < s := hb
    have hv' : b < n ∧ x (b + 1) = false := by
      simpa [Freezing1.vertexLabels, Freezing1.frozenIndices] using hv
    have hj : s - (b + 1) < s := by omega
    have he : s - b = (s - (b + 1)) + 1 := by omega
    have ht : s - ((s - (b + 1)) + 1) = b := by omega
    have hprev := law_valid hn hs (show s - (b + 1) ≤ s by omega) hF
    have hphase : s - (s - (b + 1)) = b + 1 := by omega
    rw [hphase] at hprev
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    change law x s F (s - b) {G | Alone G A (.inr b)} = 1
    rw [he, law, ite_eq_left hj, ht, Measure.bind_apply (by trivial)
      measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _G, (1 : ℝ≥0∞) ∂law x s F (s - (b + 1)) := by
        apply lintegral_congr_ae
        filter_upwards [hprev] with G hG
        have hfresh : Sum.inr b ∉ G.vertices := by
          rw [hG.vertices_eq]
          exact Reverse.fresh_freezing_label x n b
        have hAl := alone_insertLabel G b A hfresh
        simp only [Reverse.transitionLaw, hv'.2, Bool.false_eq_true, ↓reduceIte]
        exact (ae_iff_prob_eq_one measurable_from_top).mp
          ((ae_dirac_iff (by trivial)).mpr hAl)
      _ = 1 := by simp

/-- Comparison with a younger marked label from any valid initial forest.
The older label is present initially, and the younger one is born later. -/
theorem isolation_probability_le_younger {x : SignSequence} {n s t : ℕ}
    {F : Reverse.Forest} (hn : (n : ℕ∞) ≤ extinctionTime x) (hs : s ≤ n)
    (hF : Reverse.ValidAt x n s F) {A : Finset (ℕ ⊕ ℕ)}
    (hA : A ⊆ Freezing1.vertexLabels x n) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ A) (hv : v ∈ A) (huBorn : s ≤ Freezing1.birthTime n u)
    (hvBorn : Freezing1.birthTime n v < s) (ht : t ≤ Freezing1.birthTime n v) :
    (law x s F (s - t)).real {G | Alone G A u} ≤
      (law x s F (s - t)).real {G | Alone G A v} := by
  let b := Freezing1.birthTime n v
  have ht_s : t ≤ s := ht.trans hvBorn.le
  have hphase : t + (s - b) ≤ s := by dsimp [b]; omega
  have he : s - (t + (s - b)) = b - t := by dsimp [b]; omega
  have heu := integral_isolationValue x hphase F A u
  have hev := integral_isolationValue x hphase F A v
  rw [he] at heu hev
  rw [isolation_probability_eq_value x ht_s F A u,
    isolation_probability_eq_value x ht_s F A v, ← heu, ← hev]
  apply integral_mono_ae (integrable_isolationValue x A t _ u _)
    (integrable_isolationValue x A t _ v _)
  have hvalid := law_valid hn hs (show s - b ≤ s by omega) hF
  have hsb : s - (s - b) = b := by dsimp [b]; omega
  rw [hsb] at hvalid
  filter_upwards [hvalid, law_alone_at_birth hn hs hF A (hA hv) hvBorn] with G hG hAl
  have huG : u ∈ G.vertices := by
    rw [hG.vertices_eq]
    exact (Reverse.mem_phaseLabels_iff_birthTime (by dsimp [b]; omega) (hA hu)).mpr
      (hvBorn.le.trans huBorn)
  have hvG : v ∈ G.vertices := by
    rw [hG.vertices_eq]
    exact (Reverse.mem_phaseLabels_iff_birthTime (by dsimp [b]; omega) (hA hv)).mpr le_rfl
  have htphase : t + (b - t) = b := Nat.add_sub_of_le ht
  apply isolationValue_le_of_alone (by simpa only [htphase] using hG) hu hv huG hvG hAl

/-- The upper birth endpoint is permitted when its freshly born marked
label is a singleton in the specified initial forest. Actual history support
will discharge this boundary premise before conditional iteration. -/
theorem isolation_probability_le_younger_or_current_singleton
    {x : SignSequence} {n s t : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hs : s ≤ n)
    (hF : Reverse.ValidAt x n s F) {A : Finset (ℕ ⊕ ℕ)}
    (hA : A ⊆ Freezing1.vertexLabels x n) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ A) (hv : v ∈ A) (huBorn : s ≤ Freezing1.birthTime n u)
    (hvBorn : Freezing1.birthTime n v ≤ s) (ht : t ≤ Freezing1.birthTime n v)
    (hboundary : Freezing1.birthTime n v = s → Alone F A v) :
    (law x s F (s - t)).real {G | Alone G A u} ≤
      (law x s F (s - t)).real {G | Alone G A v} := by
  rcases lt_or_eq_of_le hvBorn with hvlt | hveq
  · exact isolation_probability_le_younger hn hs hF hA hu hv huBorn hvlt ht
  · have hts : t ≤ s := ht.trans hvBorn
    have huF : u ∈ F.vertices := by
      rw [hF.vertices_eq]
      exact (Reverse.mem_phaseLabels_iff_birthTime hs (hA hu)).mpr huBorn
    have hvF : v ∈ F.vertices := by
      rw [hF.vertices_eq]
      exact (Reverse.mem_phaseLabels_iff_birthTime hs (hA hv)).mpr hveq.ge
    rw [isolation_probability_eq_value x hts F A u,
      isolation_probability_eq_value x hts F A v]
    exact isolationValue_le_of_alone
      (by simpa only [Nat.add_sub_of_le hts] using hF) hu hv huF hvF (hboundary hveq)

/-- Actual continuation analogue of U34 Step 1. The oldest marked label is
present initially; younger labels are inserted during continuation, or are
initial singletons at that phase. All marked labels are present by the target
phase. -/
theorem oldest_isolation_probability_le_integral_count {x : SignSequence} {n s t : ℕ}
    {F : Reverse.Forest} (hn : (n : ℕ∞) ≤ extinctionTime x) (hs : s ≤ n)
    (ht : t ≤ s) (hF : Reverse.ValidAt x n s F) {A : Finset (ℕ ⊕ ℕ)}
    (hA : A ⊆ Freezing1.vertexLabels x n) {u : ℕ ⊕ ℕ} (hu : u ∈ A)
    (huBorn : s ≤ Freezing1.birthTime n u)
    (hyoung : ∀ v ∈ A, v ≠ u → Freezing1.birthTime n v ≤ s)
    (hboundary : ∀ v ∈ A, v ≠ u → Freezing1.birthTime n v = s → Alone F A v)
    (hborn : ∀ v ∈ A, t ≤ Freezing1.birthTime n v) :
    (law x s F (s - t)).real {G | Alone G A u} ≤
      (∫ G, (componentCount G A : ℝ) ∂law x s F (s - t)) / A.card := by
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr ⟨u, hu⟩
  have hsum : (A.card : ℝ) * (law x s F (s - t)).real {G | Alone G A u} ≤
      ∑ v ∈ A, (law x s F (s - t)).real {G | Alone G A v} := by
    calc
      _ = ∑ _v ∈ A, (law x s F (s - t)).real {G | Alone G A u} := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        by_cases he : v = u
        · subst v; exact le_rfl
        · exact isolation_probability_le_younger_or_current_singleton hn hs hF hA hu hv huBorn
            (hyoung v hv he) (hborn v hv) (hboundary v hv he)
  have hp : ∀ᵐ G ∂law x s F (s - t), A ⊆ G.vertices := by
    apply law_tracked_present hn hs (Nat.sub_le _ _) hF hA
    simpa only [Nat.sub_sub_self ht] using hborn
  have hc := sum_alone_probability_le_integral_count (law x s F (s - t)) A hp
  apply (le_div_iff₀ hcard).mpr
  simpa only [mul_comm] using hsum.trans hc

end Freezing2.ReverseContinuation
