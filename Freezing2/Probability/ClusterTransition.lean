module

public import Freezing2.Probability.CoalescenceTransition

/-!
# Exact transitions of finitely many tracked components

A finite subset of the current roots represents distinct tracked components.
The actual reverse join merges two of them precisely when both selected roots
belong to that subset. Counting supported ordered pairs gives the source's
binomial hazard and its complementary survival factor without an independence
assumption. Freezing steps do not merge existing tracked components.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Classical

namespace Freezing2.TrackedClusters

open Freezing1 ForestCoalescence

variable {V : Type*} [DecidableEq V]

/-- At least two of the specified representatives have become connected. -/
def Merger (A : Finset V) (G : RootedForest V) : Prop :=
  ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ G.root u = G.root v

/-- The forest observable agrees exactly with selection of two tracked roots. -/
theorem merger_joinChoice_iff (F : RootedForest V) {A : Finset V}
    (hA : A ⊆ F.roots) {p : V × V} (hp : p ∈ F.roots.offDiag) :
    Merger A (F.joinChoice p) ↔ p.1 ∈ A ∧ p.2 ∈ A := by
  constructor
  · rintro ⟨u, hu, v, hv, huv, h⟩
    have hru := (RootedForest.mem_roots.mp (hA hu)).2
    have hrv := (RootedForest.mem_roots.mp (hA hv)).2
    have hne : F.root u ≠ F.root v := by simpa only [hru, hrv] using huv
    have hp' := (joinChoice_root_eq_iff F hp hne).mp h
    simp only [hru, hrv] at hp'
    rcases hp' with rfl | rfl
    · exact ⟨hu, hv⟩
    · exact ⟨hv, hu⟩
  · rintro ⟨hu, hv⟩
    have hru := (RootedForest.mem_roots.mp (hA hu)).2
    have hrv := (RootedForest.mem_roots.mp (hA hv)).2
    have huv := (Finset.mem_offDiag.mp hp).2.2
    refine ⟨p.1, hu, p.2, hv, huv, ?_⟩
    apply (joinChoice_root_eq_iff F hp (by simpa only [hru, hrv] using huv)).mpr
    exact Or.inl (by simp only [hru, hrv])

theorem offDiag_filter_tracked (s A : Finset V) (hA : A ⊆ s) :
    s.offDiag.filter (fun p ↦ p.1 ∈ A ∧ p.2 ∈ A) = A.offDiag := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_offDiag]
  aesop

omit [DecidableEq V] in
/-- The real ordered-pair count also holds for empty tracked sets. -/
theorem card_offDiag_real_all (A : Finset V) :
    (A.offDiag.card : ℝ) = (A.card : ℝ) * ((A.card : ℝ) - 1) := by
  by_cases hA : A.card = 0
  · simp [hA]
  · exact card_offDiag_real A (by omega)

variable [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- Exact binomial hazard for a merger anywhere in the tracked root subset. -/
theorem joinLaw_merger (F : RootedForest V) (hF : 2 ≤ F.roots.card)
    {A : Finset V} (hA : A ⊆ F.roots) :
    F.joinLaw.real {G | Merger A G} =
      (A.card.choose 2 : ℝ) / (F.roots.card.choose 2 : ℝ) := by
  have hf : F.roots.offDiag.filter (fun p ↦ Merger A (F.joinChoice p)) = A.offDiag := by
    rw [← offDiag_filter_tracked F.roots A hA]
    apply Finset.filter_congr
    intro p hp
    exact merger_joinChoice_iff F hA hp
  change (F.joinLaw {G | Merger A G}).toReal = _
  rw [RootedForest.joinLaw_apply F hF]
  simp only [Set.mem_ofPred_eq, hf, ENNReal.toReal_div, ENNReal.toReal_natCast]
  rw [card_offDiag_real_all, card_offDiag_real_all, Nat.cast_choose_two,
    Nat.cast_choose_two]
  exact (div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0) _ _).symm

/-- Exact complementary factor, including tracked sets of size zero or one. -/
theorem joinLaw_noMerger (F : RootedForest V) (hF : 2 ≤ F.roots.card)
    {A : Finset V} (hA : A ⊆ F.roots) :
    F.joinLaw.real {G | ¬Merger A G} =
      1 - (A.card.choose 2 : ℝ) / (F.roots.card.choose 2 : ℝ) := by
  change F.joinLaw.real {G | Merger A G}ᶜ = _
  rw [probReal_compl_eq_one_sub (by trivial), joinLaw_merger F hF hA]

/-- Every prescribed unordered pair of tracked components has the same hazard. -/
theorem joinLaw_fixedPair (F : RootedForest V) (hF : 2 ≤ F.roots.card)
    {u v : V} (hu : u ∈ F.roots) (hv : v ∈ F.roots) (huv : u ≠ v) :
    F.joinLaw.real {G | G.root u = G.root v} =
      1 / (F.roots.card.choose 2 : ℝ) := by
  have hru := (RootedForest.mem_roots.mp hu).2
  have hrv := (RootedForest.mem_roots.mp hv).2
  rw [joinLaw_coalescence F hF (RootedForest.mem_roots.mp hu).1
    (RootedForest.mem_roots.mp hv).1 (by simpa only [hru, hrv] using huv),
    Nat.cast_choose_two, one_div, inv_div]

/-- Adding the new freezing label never merges previously distinct roots. -/
theorem not_merger_insertLabel (F : Reverse.Forest) (i : ℕ)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ F.roots) :
    ¬Merger A (Reverse.insertLabel F i) := by
  rintro ⟨u, hu, v, hv, huv, h⟩
  have hFu := RootedForest.mem_roots.mp (hA hu)
  have hFv := RootedForest.mem_roots.mp (hA hv)
  rw [insertLabel_root_old F i hFu.1, insertLabel_root_old F i hFv.1,
    hFu.2, hFv.2] at h
  exact huv h

/-- The exact tracked-cluster hazard in the actual phase transition.
The population is the number of roots before that reverse transition. -/
theorem transitionLaw_merger {x : SignSequence} {n i : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : Reverse.ValidAt x n (i + 1) F) {A : Finset (ℕ ⊕ ℕ)}
    (hA : A ⊆ F.roots) :
    (Reverse.transitionLaw x i F).real {G | Merger A G} =
      if x (i + 1) then
        (A.card.choose 2 : ℝ) / ((activeCount x (i + 1)).toNat.choose 2 : ℝ)
      else 0 := by
  have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
    le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast (Nat.succ_le_of_lt hi)) hn
  cases hx : x (i + 1)
  · simp [Reverse.transitionLaw, hx, Measure.real, not_merger_insertLabel F i hA]
  · have htwo : 2 ≤ F.roots.card := by
      rw [hF.roots_card]
      exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
    simp only [Reverse.transitionLaw, hx, ↓reduceIte]
    rw [joinLaw_merger F htwo hA, hF.roots_card]

/-- The source survival factor is a consequence of the actual transition law. -/
theorem transitionLaw_noMerger {x : SignSequence} {n i : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : Reverse.ValidAt x n (i + 1) F) {A : Finset (ℕ ⊕ ℕ)}
    (hA : A ⊆ F.roots) :
    (Reverse.transitionLaw x i F).real {G | ¬Merger A G} =
      1 - if x (i + 1) then
        (A.card.choose 2 : ℝ) / ((activeCount x (i + 1)).toNat.choose 2 : ℝ)
      else 0 := by
  change (Reverse.transitionLaw x i F).real {G | Merger A G}ᶜ = _
  rw [probReal_compl_eq_one_sub (by trivial), transitionLaw_merger hn hi hF hA]

/-- The marked merger of a specified unordered pair of current roots. -/
theorem transitionLaw_fixedPair {x : SignSequence} {n i : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : Reverse.ValidAt x n (i + 1) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.roots) (hv : v ∈ F.roots) (huv : u ≠ v) :
    (Reverse.transitionLaw x i F).real {G | G.root u = G.root v} =
      if x (i + 1) then
        1 / ((activeCount x (i + 1)).toNat.choose 2 : ℝ)
      else 0 := by
  have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
    le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast (Nat.succ_le_of_lt hi)) hn
  have hFu := RootedForest.mem_roots.mp hu
  have hFv := RootedForest.mem_roots.mp hv
  cases hx : x (i + 1)
  · simp [Reverse.transitionLaw, hx, Measure.real,
      insertLabel_root_old F i hFu.1, insertLabel_root_old F i hFv.1, hFu.2, hFv.2, huv]
  · have htwo : 2 ≤ F.roots.card := by
      rw [hF.roots_card]
      exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
    simp only [Reverse.transitionLaw, hx, ↓reduceIte]
    rw [joinLaw_fixedPair F htwo hu hv huv, hF.roots_card]

omit [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V] in
/-- The ordered merger is observable from the surviving component root:
for distinct original roots, making the root of `v` equal to `u` selects the
order `(u,v)` and not its reverse. -/
theorem joinChoice_root_eq_iff_ordered (F : RootedForest V) {p : V × V}
    (hp : p ∈ F.roots.offDiag) {u v : V} (hv : v ∈ F.roots) (huv : u ≠ v) :
    (F.joinChoice p).root v = u ↔ p = (u, v) := by
  have hrv := (RootedForest.mem_roots.mp hv).2
  simp only [RootedForest.joinChoice, dite_eq_left hp, RootedForest.join, hrv]
  constructor
  · intro h
    by_cases hvp : v = p.2
    · rw [ite_eq_left hvp] at h
      exact Prod.ext h hvp.symm
    · rw [ite_eq_right hvp] at h
      exact False.elim (huv h.symm)
  · rintro rfl
    simp

/-- The source planar factor is the probability of this actual oriented
forest transition, not an additional independent orientation assumption. -/
theorem joinLaw_orderedPair (F : RootedForest V) (hF : 2 ≤ F.roots.card)
    {u v : V} (hu : u ∈ F.roots) (hv : v ∈ F.roots) (huv : u ≠ v) :
    F.joinLaw.real {G | G.root v = u} =
      1 / (2 * (F.roots.card.choose 2 : ℝ)) := by
  have hf : F.roots.offDiag.filter (fun p ↦ (F.joinChoice p).root v = u) =
      F.roots.offDiag.filter (fun p ↦ p = (u, v)) := by
    apply Finset.filter_congr
    intro p hp
    exact joinChoice_root_eq_iff_ordered F hp hv huv
  have hprob : F.joinLaw.real {G | G.root v = u} =
      (uniformRootPair F.roots).real {(u, v)} := by
    change (F.joinLaw {G | G.root v = u}).toReal = _
    rw [RootedForest.joinLaw_apply F hF]
    simp only [Set.mem_ofPred_eq, hf]
    simp only [uniformRootPair, Measure.real, Measure.uniformOfFinset_apply,
      Set.mem_singleton_iff]
  rw [hprob, uniformRootPair_ordered F.roots hu hv huv, Nat.cast_choose_two]
  congr 1
  ring

/-- The marked planar merger factor at a genuine reverse transition. -/
theorem transitionLaw_orderedPair {x : SignSequence} {n i : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : Reverse.ValidAt x n (i + 1) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.roots) (hv : v ∈ F.roots) (huv : u ≠ v) :
    (Reverse.transitionLaw x i F).real {G | G.root v = u} =
      if x (i + 1) then
        1 / (2 * ((activeCount x (i + 1)).toNat.choose 2 : ℝ))
      else 0 := by
  have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
    le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast (Nat.succ_le_of_lt hi)) hn
  have hFv := RootedForest.mem_roots.mp hv
  cases hx : x (i + 1)
  · simp [Reverse.transitionLaw, hx, Measure.real,
      insertLabel_root_old F i hFv.1, hFv.2, Ne.symm huv]
  · have htwo : 2 ≤ F.roots.card := by
      rw [hF.roots_card]
      exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
    simp only [Reverse.transitionLaw, hx, ↓reduceIte]
    rw [joinLaw_orderedPair F htwo hu hv huv, hF.roots_card]

end Freezing2.TrackedClusters
