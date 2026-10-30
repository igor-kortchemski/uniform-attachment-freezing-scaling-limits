module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.ReverseStampedForest

/-!
# Schedule support of reverse edge timestamps

The positive edge timestamps at reverse phase `i` must be exactly the
attachment indices in `(i,n]`, each occurring once. Root timestamps are zero.
These are necessary inputs to the canonical birth-ID representation; equality
in law with the forward construction is not assumed.
-/

@[expose] public section

namespace Freezing1.ReverseStamped

open MeasureTheory
open scoped Classical ENNReal

def attachmentTimes (x : SignSequence) (n i : ℕ) : Finset ℕ :=
  (Finset.Ioc i n).filter fun t => x t = true

def positiveEdgeVertices (F : Forest) : Finset (ℕ ⊕ ℕ) :=
  F.forest.vertices.filter fun v => F.edgeTime v ≠ 0

structure TimesValidAt (x : SignSequence) (n i : ℕ) (F : Forest) : Prop where
  root_zero : ∀ v ∈ F.forest.vertices, F.edgeTime v = 0 ↔ v ∈ F.forest.roots
  range : ∀ v ∈ F.forest.vertices, F.edgeTime v ≠ 0 →
    i < F.edgeTime v ∧ F.edgeTime v ≤ n ∧ x (F.edgeTime v) = true
  injective : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
    F.edgeTime u ≠ 0 → F.edgeTime v ≠ 0 → F.edgeTime u = F.edgeTime v → u = v
  image_eq : (positiveEdgeVertices F).image F.edgeTime = attachmentTimes x n i

theorem attachmentTimes_top (x : SignSequence) (n : ℕ) : attachmentTimes x n n = ∅ := by
  simp [attachmentTimes]

theorem attachmentTimes_attachment (x : SignSequence) {n i : ℕ}
    (hi : i < n) (hx : x (i + 1) = true) :
    attachmentTimes x n i = insert (i + 1) (attachmentTimes x n (i + 1)) := by
  ext t
  simp only [attachmentTimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_insert]
  constructor
  · rintro ⟨⟨hit, htn⟩, hxt⟩
    by_cases ht : t = i + 1
    · exact Or.inl ht
    · exact Or.inr ⟨⟨by omega, htn⟩, hxt⟩
  · rintro (rfl | ⟨⟨hit, htn⟩, hxt⟩)
    · exact ⟨⟨by omega, by omega⟩, hx⟩
    · exact ⟨⟨by omega, htn⟩, hxt⟩

theorem attachmentTimes_freezing (x : SignSequence) (n i : ℕ)
    (hx : x (i + 1) = false) :
    attachmentTimes x n i = attachmentTimes x n (i + 1) := by
  ext t
  simp only [attachmentTimes, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hit, htn⟩, hxt⟩
    have ht : t ≠ i + 1 := by intro he; rw [he, hx] at hxt; contradiction
    exact ⟨⟨by omega, htn⟩, hxt⟩
  · rintro ⟨⟨hit, htn⟩, hxt⟩
    exact ⟨⟨by omega, htn⟩, hxt⟩

theorem initial_times_valid (x : SignSequence) (n : ℕ) :
    TimesValidAt x n n (initial x n) := by
  constructor
  · intro v hv
    simpa [initial, Reverse.initial, RootedForest.roots, RootedForest.isolated] using hv
  · intro v _ hv
    simp [initial] at hv
  · intro u _ v _ hu
    simp [initial] at hu
  · simp [positiveEdgeVertices, initial, attachmentTimes_top]

/-- Giving the new parent edge a positive time removes precisely its child
endpoint from the zero-timestamp roots. -/
theorem joinChoice_root_zero (F : Forest) {t : ℕ} (ht : t ≠ 0)
    (hzero : ∀ v ∈ F.forest.vertices, F.edgeTime v = 0 ↔ v ∈ F.forest.roots)
    {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)} (hp : p ∈ F.forest.roots.offDiag) :
    ∀ v ∈ (joinChoice F t p).forest.vertices,
      (joinChoice F t p).edgeTime v = 0 ↔ v ∈ (joinChoice F t p).forest.roots := by
  intro v hv
  simp only [ReverseStamped.joinChoice, dite_eq_left hp] at hv ⊢
  rw [RootedForest.join_roots]
  by_cases hvb : v = p.2
  · subst v
    simp [ht]
  · simpa [hvb] using hzero v hv

/-- Every old edge time is larger than the new reverse step time. Therefore
updating the newly attached root cannot collide with an existing edge label. -/
theorem joinChoice_edgeTime_injective (F : Forest) {t : ℕ}
    (hrange : ∀ v ∈ F.forest.vertices, F.edgeTime v ≠ 0 → t < F.edgeTime v)
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u ≠ 0 → F.edgeTime v ≠ 0 → F.edgeTime u = F.edgeTime v → u = v)
    {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)} (hp : p ∈ F.forest.roots.offDiag) :
    ∀ u ∈ (joinChoice F t p).forest.vertices, ∀ v ∈ (joinChoice F t p).forest.vertices,
      (joinChoice F t p).edgeTime u ≠ 0 → (joinChoice F t p).edgeTime v ≠ 0 →
      (joinChoice F t p).edgeTime u = (joinChoice F t p).edgeTime v → u = v := by
  intro u hu v hv hut hvt he
  simp only [ReverseStamped.joinChoice, dite_eq_left hp] at hu hv hut hvt he
  by_cases hub : u = p.2
  · subst u
    by_cases hvb : v = p.2
    · exact hvb.symm
    · simp only [Function.update_self, Function.update_of_ne hvb] at he hvt
      have := hrange v hv hvt
      omega
  · by_cases hvb : v = p.2
    · subst v
      simp only [Function.update_self, Function.update_of_ne hub] at he hut
      have := hrange u hu hut
      omega
    · simp only [Function.update_of_ne hub, Function.update_of_ne hvb] at he hut hvt
      exact hinj u hu v hv hut hvt he

theorem joinChoice_edgeTime_image (F : Forest) {t : ℕ} (ht : t ≠ 0)
    {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)} (hp : p ∈ F.forest.roots.offDiag)
    (hb : F.edgeTime p.2 = 0) :
    (positiveEdgeVertices (joinChoice F t p)).image (joinChoice F t p).edgeTime =
      insert t ((positiveEdgeVertices F).image F.edgeTime) := by
  ext a
  simp only [positiveEdgeVertices, ReverseStamped.joinChoice, dite_eq_left hp,
    Finset.mem_image, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨v, ⟨hv, hnz⟩, he⟩
    by_cases hvb : v = p.2
    · subst v
      exact Or.inl (by simpa using he.symm)
    · exact Or.inr ⟨v, ⟨hv, by simpa [hvb] using hnz⟩, by simpa [hvb] using he⟩
  · rintro (rfl | ⟨v, ⟨hv, hnz⟩, he⟩)
    · exact ⟨p.2, ⟨(RootedForest.mem_roots.mp (Finset.mem_offDiag.mp hp).2.1).1,
        by simpa using ht⟩, by simp⟩
    · have hvb : v ≠ p.2 := by
        intro heq
        exact hnz (heq ▸ hb)
      exact ⟨v, ⟨hv, by simpa [hvb] using hnz⟩, by simpa [hvb] using he⟩

/-- A legal reverse merge adds exactly its own attachment time, preserving
uniqueness and the strict lower bound on all previously created edge times. -/
theorem TimesValidAt.joinChoice {x : SignSequence} {n i : ℕ} {F : Forest}
    (hF : TimesValidAt x n (i + 1) F) (hi : i < n) (hx : x (i + 1) = true)
    {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)} (hp : p ∈ F.forest.roots.offDiag) :
    TimesValidAt x n i (joinChoice F (i + 1) p) := by
  constructor
  · exact joinChoice_root_zero F (Nat.succ_ne_zero i) hF.root_zero hp
  · intro v hv hnz
    simp only [ReverseStamped.joinChoice, dite_eq_left hp] at hv hnz ⊢
    by_cases hvb : v = p.2
    · subst v
      simpa using (show i < i + 1 ∧ i + 1 ≤ n ∧ x (i + 1) = true from
        ⟨by omega, by omega, hx⟩)
    · simp only [Function.update_of_ne hvb] at hnz ⊢
      obtain ⟨hlo, hup, hsign⟩ := hF.range v hv hnz
      exact ⟨by omega, hup, hsign⟩
  · exact joinChoice_edgeTime_injective F (fun v hv hnz => (hF.range v hv hnz).1)
      hF.injective hp
  · have hbroot := (Finset.mem_offDiag.mp hp).2.1
    have hb := (hF.root_zero p.2 (RootedForest.mem_roots.mp hbroot).1).mpr hbroot
    rw [joinChoice_edgeTime_image F (Nat.succ_ne_zero i) hp hb, hF.image_eq,
      attachmentTimes_attachment x hi hx]

theorem insertLabel_edgeTime_image (F : Forest) (i : ℕ)
    (hfresh : Sum.inr i ∉ F.forest.vertices) :
    (positiveEdgeVertices (insertLabel F i)).image (insertLabel F i).edgeTime =
      (positiveEdgeVertices F).image F.edgeTime := by
  ext a
  simp only [positiveEdgeVertices, ReverseStamped.insertLabel, dite_eq_right hfresh,
    RootedForest.adjoin_vertices, Finset.mem_image, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨v, ⟨hv, hnz⟩, he⟩
    have hvi : v ≠ Sum.inr i := by intro h; simp [h] at hnz
    exact ⟨v, ⟨hv.resolve_left hvi, by simpa [hvi] using hnz⟩,
      by simpa [hvi] using he⟩
  · rintro ⟨v, ⟨hv, hnz⟩, he⟩
    have hvi : v ≠ Sum.inr i := fun h => hfresh (h ▸ hv)
    exact ⟨v, ⟨Or.inr hv, by simpa [hvi] using hnz⟩, by simpa [hvi] using he⟩

/-- A freezing-label insertion creates a new root and no edge; its timestamp
image therefore remains exactly the attachment times at the next phase. -/
theorem TimesValidAt.insertLabel {x : SignSequence} {n i : ℕ} {F : Forest}
    (hF : TimesValidAt x n (i + 1) F) (hx : x (i + 1) = false)
    (hfresh : Sum.inr i ∉ F.forest.vertices) : TimesValidAt x n i (insertLabel F i) := by
  constructor
  · intro v hv
    simp only [ReverseStamped.insertLabel, dite_eq_right hfresh, RootedForest.adjoin_vertices] at hv ⊢
    rw [RootedForest.adjoin_roots]
    by_cases hvi : v = Sum.inr i
    · simp [hvi]
    · have hvold := (Finset.mem_insert.mp hv).resolve_left hvi
      simpa [hvi] using hF.root_zero v hvold
  · intro v hv hnz
    simp only [ReverseStamped.insertLabel, dite_eq_right hfresh, RootedForest.adjoin_vertices] at hv hnz ⊢
    have hvi : v ≠ Sum.inr i := by intro h; simp [h] at hnz
    simp only [Function.update_of_ne hvi] at hnz ⊢
    obtain ⟨hlo, hup, hsign⟩ := hF.range v ((Finset.mem_insert.mp hv).resolve_left hvi) hnz
    exact ⟨by omega, hup, hsign⟩
  · intro u hu v hv hunz hvnz he
    simp only [ReverseStamped.insertLabel, dite_eq_right hfresh, RootedForest.adjoin_vertices] at hu hv hunz hvnz he
    have hui : u ≠ Sum.inr i := by intro h; simp [h] at hunz
    have hvi : v ≠ Sum.inr i := by intro h; simp [h] at hvnz
    simp only [Function.update_of_ne hui, Function.update_of_ne hvi] at hunz hvnz he
    exact hF.injective u ((Finset.mem_insert.mp hu).resolve_left hui)
      v ((Finset.mem_insert.mp hv).resolve_left hvi) hunz hvnz he
  · rw [insertLabel_edgeTime_image F i hfresh, hF.image_eq,
      attachmentTimes_freezing x n i hx]

theorem joinLaw_apply (F : Forest) (t : ℕ) (htwo : 2 ≤ F.forest.roots.card)
    (A : Set Forest) :
    joinLaw F t A = ((F.forest.roots.offDiag.filter fun p => joinChoice F t p ∈ A).card : ℝ≥0∞) /
      F.forest.roots.offDiag.card := by
  rw [joinLaw, ite_eq_left htwo, Measure.map_apply (measurable_of_countable _) (by trivial),
    uniformRootPair, Measure.uniformOfFinset_apply]
  rfl

theorem joinLaw_ae (F : Forest) (t : ℕ) (htwo : 2 ≤ F.forest.roots.card)
    (P : Forest → Prop) (hP : ∀ p ∈ F.forest.roots.offDiag, P (joinChoice F t p)) :
    ∀ᵐ F' ∂joinLaw F t, P F' := by
  apply (ae_iff_prob_eq_one measurable_from_top).mpr
  rw [joinLaw_apply F t htwo]
  have hf : F.forest.roots.offDiag.filter (fun p => joinChoice F t p ∈ {F' | P F'}) =
      F.forest.roots.offDiag := Finset.filter_eq_self.mpr hP
  rw [hf]
  exact ENNReal.div_self
    (by exact_mod_cast (offDiag_nonempty_of_two_le_card htwo).card_pos.ne')
    (ENNReal.natCast_ne_top _)

/-- The genuine timestamped transition preserves exact schedule support. -/
theorem transitionLaw_times_valid {x : SignSequence} {n i : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : Reverse.ValidAt x n (i + 1) F.forest) (ht : TimesValidAt x n (i + 1) F) :
    ∀ᵐ F' ∂transitionLaw x i F, TimesValidAt x n i F' := by
  cases hx : x (i + 1)
  · have hfresh : Sum.inr i ∉ F.forest.vertices := by
      rw [hF.vertices_eq]
      exact Reverse.fresh_freezing_label x n i
    simp only [transitionLaw, hx, Bool.false_eq_true, ↓reduceIte]
    exact (ae_dirac_iff (by trivial)).mpr (ht.insertLabel hx hfresh)
  · have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
      le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast (Nat.succ_le_of_lt hi)) hn
    have htwo : 2 ≤ F.forest.roots.card := by
      rw [hF.roots_card]
      exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
    simp only [transitionLaw, hx, ↓reduceIte]
    exact joinLaw_ae F (i + 1) htwo (TimesValidAt x n i)
      (fun _ hp => ht.joinChoice hi hx hp)

/-- Every actual reverse phase has exactly the schedule's remaining positive
step labels, each assigned to precisely one parent edge. -/
theorem lawAfter_times_valid (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k ≤ n) :
    ∀ᵐ F ∂lawAfter x n k, TimesValidAt x n (n - k) F := by
  induction k with
  | zero => simpa [lawAfter] using initial_times_valid x n
  | succ k ih =>
    have hkn : k < n := by omega
    have ih := ih (by omega)
    have hphase : n - k = n - (k + 1) + 1 := by omega
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [lawAfter, ite_eq_left hkn, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _F, (1 : ℝ≥0∞) ∂lawAfter x n k := by
        apply lintegral_congr_ae
        filter_upwards [ih, lawAfter_forest_valid x n k hn (by omega)] with F ht hF
        rw [hphase] at ht hF
        exact (ae_iff_prob_eq_one measurable_from_top).mp
          (transitionLaw_times_valid hn (by omega) hF ht)
      _ = 1 := by simp

theorem treeLaw_times_valid (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂treeLaw x n, TimesValidAt x n 0 F := by
  simpa only [treeLaw, Nat.sub_self] using lawAfter_times_valid x n n hn le_rfl

/-- With one component, incoming edge timestamps distinguish every vertex:
the unique root has identifier zero, and nonroots have distinct positive IDs. -/
theorem TimesValidAt.edgeTime_injective_of_one_root {x : SignSequence} {n i : ℕ} {F : Forest}
    (hF : TimesValidAt x n i F) (hone : F.forest.roots.card = 1) :
    ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v := by
  intro u hu v hv he
  by_cases huz : F.edgeTime u = 0
  · have hvz : F.edgeTime v = 0 := he ▸ huz
    exact (Finset.card_le_one.mp hone.le) u ((hF.root_zero u hu).mp huz)
      v ((hF.root_zero v hv).mp hvz)
  · have hvnz : F.edgeTime v ≠ 0 := by simpa only [← he] using huz
    exact hF.injective u hu v hv huz hvnz he

/-- The canonical incoming-time IDs have exactly the forward birth-ID set. -/
theorem TimesValidAt.edgeTime_image_of_one_root {x : SignSequence} {n : ℕ} {F : Forest}
    (hF : TimesValidAt x n 0 F) (hone : F.forest.roots.card = 1) :
    F.forest.vertices.image F.edgeTime = insert 0 (attachmentTimes x n 0) := by
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (show 0 < F.forest.roots.card by omega)
  have hrV := (RootedForest.mem_roots.mp hr).1
  have hrt := (hF.root_zero r hrV).mpr hr
  rw [← hF.image_eq]
  ext t
  simp only [Finset.mem_image, Finset.mem_insert, positiveEdgeVertices, Finset.mem_filter]
  constructor
  · rintro ⟨v, hv, rfl⟩
    by_cases hz : F.edgeTime v = 0
    · exact Or.inl hz
    · exact Or.inr ⟨v, ⟨hv, hz⟩, rfl⟩
  · rintro (rfl | ⟨v, ⟨hv, _⟩, he⟩)
    · exact ⟨r, hrV, hrt⟩
    · exact ⟨v, hv, he⟩

/-- Actual terminal stamped forests admit canonical birth-time identifiers,
including when the schedule reaches extinction exactly at the terminal step. -/
theorem treeLaw_canonical_ids (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂treeLaw x n,
      (∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
        F.edgeTime u = F.edgeTime v → u = v) ∧
      F.forest.vertices.image F.edgeTime = insert 0 (attachmentTimes x n 0) := by
  filter_upwards [treeLaw_times_valid x n hn,
    lawAfter_forest_valid x n n hn le_rfl] with F ht hF
  have hone : F.forest.roots.card = 1 := by
    simpa only [Nat.sub_self, activeCount_zero, Int.toNat_one] using hF.roots_card
  exact ⟨ht.edgeTime_injective_of_one_root hone, ht.edgeTime_image_of_one_root hone⟩

end Freezing1.ReverseStamped
