module

public import Freezing2.Companion.ReverseTimestampSupport

/-!
# Unique stamped reverse transitions and their exact masses

The new positive timestamp identifies the second root, and the new parent
identifies the first root. Thus precisely one legal ordered pair produces a
specified next stamped forest, as used in the source proof of N01.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Classical

namespace Freezing2.ReverseStamped

abbrev Forest := Freezing1.ReverseStamped.Forest

/-- A positive new timestamp and its parent recover both roots of the chosen
ordered pair. The zero-root premise is proved for every actual reverse state. -/
theorem joinChoice_injOn (F : Forest) {t : ℕ} (ht : 0 < t)
    (hz : ∀ r ∈ F.forest.roots, F.edgeTime r = 0) :
    Set.InjOn (Freezing1.ReverseStamped.joinChoice F t) (F.forest.roots.offDiag : Set _) := by
  intro p hp q hq he
  change p ∈ F.forest.roots.offDiag at hp
  change q ∈ F.forest.roots.offDiag at hq
  have hb : p.2 = q.2 := by
    by_contra hne
    have htimes := congrArg (fun G : Forest ↦ G.edgeTime p.2) he
    have hpzero := hz p.2 (Finset.mem_offDiag.mp hp).2.1
    simp only [Freezing1.ReverseStamped.joinChoice, dite_eq_left hp, dite_eq_left hq,
      Function.update_self, Function.update_of_ne hne, hpzero] at htimes
    omega
  have hparents := congrArg (fun G : Forest ↦ G.forest.parent p.2) he
  have ha : p.1 = q.1 := by
    simpa only [Freezing1.ReverseStamped.joinChoice, dite_eq_left hp, dite_eq_left hq,
      Freezing1.RootedForest.join, ite_true, hb] using hparents
  exact Prod.ext ha hb

/-- The mass of the next stamped forest is the actual uniform ordered-pair
factor; it is not inferred from the scalar history identity. -/
theorem joinLaw_apply_singleton (F : Forest) {t : ℕ} (ht : 0 < t)
    (hz : ∀ r ∈ F.forest.roots, F.edgeTime r = 0)
    (htwo : 2 ≤ F.forest.roots.card) {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)}
    (hp : p ∈ F.forest.roots.offDiag) :
    Freezing1.ReverseStamped.joinLaw F t {Freezing1.ReverseStamped.joinChoice F t p} =
      (F.forest.roots.offDiag.card : ℝ≥0∞)⁻¹ := by
  rw [Freezing1.ReverseStamped.joinLaw_apply F t htwo]
  have hf : F.forest.roots.offDiag.filter
      (fun q ↦ Freezing1.ReverseStamped.joinChoice F t q ∈
        ({Freezing1.ReverseStamped.joinChoice F t p} : Set Forest)) = {p} := by
    ext q
    simp only [Finset.mem_filter, Set.mem_singleton_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨hq, he⟩
      exact joinChoice_injOn F ht hz hq hp he
    · rintro rfl
      exact ⟨hp, rfl⟩
  simp only [Set.mem_singleton_iff] at hf ⊢
  rw [hf, Finset.card_singleton, Nat.cast_one, one_div]

/-- Specialization to the proved timestamp invariant at an actual reverse
phase, including the source's at-or-before-extinction horizon. -/
theorem transition_attachment_singleton {x : Freezing1.SignSequence} {n i : ℕ}
    {F : Forest} (hF : Freezing1.Reverse.ValidAt x n (i + 1) F.forest)
    (hT : Freezing1.ReverseStamped.TimesValidAt x n (i + 1) F)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hi : i < n)
    (hxi : x (i + 1) = true) {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)}
    (hp : p ∈ F.forest.roots.offDiag) :
    Freezing1.ReverseStamped.transitionLaw x i F
      {Freezing1.ReverseStamped.joinChoice F (i + 1) p} =
      (((Freezing1.activeCount x (i + 1)).toNat *
        ((Freezing1.activeCount x (i + 1)).toNat - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
  have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ Freezing1.extinctionTime x :=
    le_trans (by exact_mod_cast Nat.succ_le_of_lt hi) hn
  have htwo : 2 ≤ F.forest.roots.card := by
    rw [hF.roots_card]
    exact Freezing1.two_le_activeCount_toNat_succ_of_attachment hiτ hxi
  have hz : ∀ r ∈ F.forest.roots, F.edgeTime r = 0 := by
    intro r hr
    exact (hT.root_zero r (Freezing1.RootedForest.mem_roots.mp hr).1).mpr hr
  simp only [Freezing1.ReverseStamped.transitionLaw, hxi, ite_true]
  rw [joinLaw_apply_singleton F (by omega) hz htwo hp,
    Freezing1.card_offDiag_eq_mul_pred, hF.roots_card]

end Freezing2.ReverseStamped
