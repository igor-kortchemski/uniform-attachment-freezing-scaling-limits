module

public import Freezing2.Probability.ClusterTransition
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The actual number of components meeting specified vertices

The tracked component set is the image of a fixed vertex set under the current
root map. A supported reverse join lowers its cardinality by one exactly when
both selected roots belong to this image. Freezing preserves the count once
all tracked vertices are present. The expected decrement is derived from the
concrete kernel and the counted merger probability.
-/

@[expose] public section

open MeasureTheory
open scoped Classical ENNReal

namespace Freezing2.TrackedClusters

open Freezing1 ForestCoalescence

variable {V : Type*} [DecidableEq V]

/-- The distinct current roots of components containing a tracked vertex. -/
def componentRoots (F : RootedForest V) (A : Finset V) : Finset V := A.image F.root

/-- Number of actual components meeting the tracked vertex set. -/
def componentCount (F : RootedForest V) (A : Finset V) : ℕ := (componentRoots F A).card

theorem componentRoots_subset_roots (F : RootedForest V) {A : Finset V}
    (hA : A ⊆ F.vertices) : componentRoots F A ⊆ F.roots := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
  exact F.root_mem_roots (hA hv)

theorem componentCount_pos (F : RootedForest V) {A : Finset V} (hA : A.Nonempty) :
    0 < componentCount F A := Finset.card_pos.mpr (hA.image F.root)

theorem componentCount_le_card (F : RootedForest V) (A : Finset V) :
    componentCount F A ≤ A.card := Finset.card_image_le

theorem componentCount_le_rootCount (F : RootedForest V) {A : Finset V}
    (hA : A ⊆ F.vertices) : componentCount F A ≤ F.roots.card :=
  Finset.card_le_card (componentRoots_subset_roots F hA)

/-- Replacing an element already in a finite set erases its old value and
inserts its replacement. -/
theorem image_replace_of_mem (R : Finset V) (a : V) {b : V} (hb : b ∈ R) :
    R.image (fun r ↦ if r = b then a else r) = insert a (R.erase b) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨r, hr, rfl⟩
    by_cases h : r = b
    · simp [h]
    · simp only [ite_eq_right h]
      exact Or.inr ⟨h, hr⟩
  · rintro (rfl | ⟨hzb, hz⟩)
    · exact ⟨b, hb, by simp⟩
    · exact ⟨z, hz, by simp [hzb]⟩

theorem image_replace_of_not_mem (R : Finset V) (a : V) {b : V} (hb : b ∉ R) :
    R.image (fun r ↦ if r = b then a else r) = R := by
  calc
    _ = R.image id := Finset.image_congr (fun r hr ↦ by
      have h : r ≠ b := fun he ↦ hb (he ▸ hr)
      simp only [ite_eq_right h, id_eq])
    _ = R := Finset.image_id

/-- The elementary finite-set count behind the tracked-cluster decrement. -/
theorem card_image_replace_add (R : Finset V) {a b : V} (hab : a ≠ b) :
    (R.image (fun r ↦ if r = b then a else r)).card +
      (if a ∈ R ∧ b ∈ R then 1 else 0) = R.card := by
  by_cases hb : b ∈ R
  · rw [image_replace_of_mem R a hb]
    by_cases ha : a ∈ R
    · rw [Finset.card_insert_of_mem (Finset.mem_erase.mpr ⟨hab, ha⟩)]
      simpa only [ha, hb, and_self, ite_true] using Finset.card_erase_add_one hb
    · rw [Finset.card_insert_of_notMem (by intro h; exact ha (Finset.mem_erase.mp h).2)]
      simpa only [ha, false_and, ite_false, add_zero] using Finset.card_erase_add_one hb
  · rw [image_replace_of_not_mem R a hb]
    simp [hb]

/-- The component-set update is the actual root-map update of the join. -/
theorem componentRoots_joinChoice (F : RootedForest V) (A : Finset V)
    {p : V × V} (hp : p ∈ F.roots.offDiag) :
    componentRoots (F.joinChoice p) A =
      (componentRoots F A).image (fun r ↦ if r = p.2 then p.1 else r) := by
  simp only [componentRoots, Finset.image_image, RootedForest.joinChoice,
    dite_eq_left hp, RootedForest.join, Function.comp_def]

/-- Exact deterministic decrement for every supported ordered choice. -/
theorem componentCount_joinChoice_add (F : RootedForest V) (A : Finset V)
    {p : V × V} (hp : p ∈ F.roots.offDiag) :
    componentCount (F.joinChoice p) A +
      (if p.1 ∈ componentRoots F A ∧ p.2 ∈ componentRoots F A then 1 else 0) =
        componentCount F A := by
  unfold componentCount
  rw [componentRoots_joinChoice F A hp]
  exact card_image_replace_add _ (Finset.mem_offDiag.mp hp).2.2

/-- Once every tracked vertex exists, a freezing insertion changes none of
its component roots. This premise will be discharged on the intended blocks. -/
theorem componentRoots_insertLabel (F : Reverse.Forest) (i : ℕ)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ F.vertices) :
    componentRoots (Reverse.insertLabel F i) A = componentRoots F A := by
  apply Finset.image_congr
  intro v hv
  exact insertLabel_root_old F i (hA hv)

theorem componentCount_insertLabel (F : Reverse.Forest) (i : ℕ)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ F.vertices) :
    componentCount (Reverse.insertLabel F i) A = componentCount F A :=
  congrArg Finset.card (componentRoots_insertLabel F i hA)

variable [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The decrement indicator is the actual tracked-merger event. -/
theorem joinLaw_ae_componentCount (F : RootedForest V) (hF : 2 ≤ F.roots.card)
    {A : Finset V} (hA : A ⊆ F.vertices) :
    ∀ᵐ G ∂F.joinLaw, componentCount G A +
      (if Merger (componentRoots F A) G then 1 else 0) = componentCount F A := by
  apply F.joinLaw_ae hF
  intro p hp
  rw [merger_joinChoice_iff F (componentRoots_subset_roots F hA) hp]
  split_ifs with hc <;> simpa [hc] using
    componentCount_joinChoice_add F A hp

omit [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V] in
/-- The count is bounded by the finite number of tracked vertices under every
probability law on forests, not only under the transition support. -/
theorem integrable_componentCount (μ : Measure (RootedForest V)) [IsFiniteMeasure μ]
    (A : Finset V) : Integrable (fun G ↦ (componentCount G A : ℝ)) μ := by
  apply Integrable.mono' (integrable_const (A.card : ℝ))
    (measurable_from_top.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun G ↦ by
    simp only [Real.norm_natCast]
    exact_mod_cast componentCount_le_card G A

/-- The expected join decrement is obtained by integrating the actual event
indicator, with no postulated expectation recursion. -/
theorem integral_joinLaw_componentCount (F : RootedForest V) (hF : 2 ≤ F.roots.card)
    {A : Finset V} (hA : A ⊆ F.vertices) :
    (∫ G, (componentCount G A : ℝ) ∂F.joinLaw) = (componentCount F A : ℝ) -
      ((componentCount F A).choose 2 : ℝ) / (F.roots.card.choose 2 : ℝ) := by
  let E : Set (RootedForest V) := {G | Merger (componentRoots F A) G}
  have hE : MeasurableSet E := by trivial
  have hi : Integrable (E.indicator (fun _ ↦ (1 : ℝ))) F.joinLaw :=
    (integrable_const 1).indicator hE
  have heq : (fun G ↦ (componentCount G A : ℝ) + E.indicator (fun _ ↦ (1 : ℝ)) G)
      =ᵐ[F.joinLaw] fun _ ↦ (componentCount F A : ℝ) := by
    filter_upwards [joinLaw_ae_componentCount F hF hA] with G hG
    by_cases he : G ∈ E
    · simp only [Set.indicator_of_mem he]
      change Merger (componentRoots F A) G at he
      rw [ite_eq_left he] at hG
      exact_mod_cast hG
    · simp only [Set.indicator_of_notMem he, add_zero]
      change ¬Merger (componentRoots F A) G at he
      rw [ite_eq_right he, add_zero] at hG
      exact_mod_cast hG
  have hint : (∫ G, E.indicator (fun _ ↦ (1 : ℝ)) G ∂F.joinLaw) = F.joinLaw.real E := by
    exact integral_indicator_one hE
  have h := integral_congr_ae heq
  rw [integral_add (integrable_componentCount F.joinLaw A) hi,
    hint, integral_const, probReal_univ, one_smul] at h
  have hp := joinLaw_merger F hF (componentRoots_subset_roots F hA)
  change F.joinLaw.real E = _ at hp
  rw [hp] at h
  exact eq_sub_of_add_eq h

/-- The genuine source step lowers the number of tracked components by
exactly the indicator of a merger between two of their current roots. -/
theorem transitionLaw_ae_componentCount {x : SignSequence} {n i : ℕ}
    {F : Reverse.Forest} (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : Reverse.ValidAt x n (i + 1) F) {A : Finset (ℕ ⊕ ℕ)}
    (hA : A ⊆ F.vertices) :
    ∀ᵐ G ∂Reverse.transitionLaw x i F, componentCount G A +
      (if Merger (componentRoots F A) G then 1 else 0) = componentCount F A := by
  have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
    le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast (Nat.succ_le_of_lt hi)) hn
  cases hx : x (i + 1)
  · simp only [Reverse.transitionLaw, hx, Bool.false_eq_true, ↓reduceIte]
    apply (ae_dirac_iff (by trivial)).mpr
    rw [componentCount_insertLabel F i hA,
      ite_eq_right (not_merger_insertLabel F i (componentRoots_subset_roots F hA)), add_zero]
  · have htwo : 2 ≤ F.roots.card := by
      rw [hF.roots_card]
      exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
    simp only [Reverse.transitionLaw, hx, ↓reduceIte]
    exact joinLaw_ae_componentCount F htwo hA

/-- The expected component count after an actual reverse step. All tracked
vertices must already be present; birth insertions are not silently ignored. -/
theorem integral_transitionLaw_componentCount {x : SignSequence} {n i : ℕ}
    {F : Reverse.Forest} (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : Reverse.ValidAt x n (i + 1) F) {A : Finset (ℕ ⊕ ℕ)}
    (hA : A ⊆ F.vertices) :
    (∫ G, (componentCount G A : ℝ) ∂Reverse.transitionLaw x i F) =
      (componentCount F A : ℝ) - if x (i + 1) then
        ((componentCount F A).choose 2 : ℝ) /
          ((activeCount x (i + 1)).toNat.choose 2 : ℝ)
      else 0 := by
  have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
    le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast (Nat.succ_le_of_lt hi)) hn
  cases hx : x (i + 1)
  · simp [Reverse.transitionLaw, hx, componentCount_insertLabel F i hA]
  · have htwo : 2 ≤ F.roots.card := by
      rw [hF.roots_card]
      exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
    simp only [Reverse.transitionLaw, hx, ↓reduceIte]
    rw [integral_joinLaw_componentCount F htwo hA, hF.roots_card]

end Freezing2.TrackedClusters
