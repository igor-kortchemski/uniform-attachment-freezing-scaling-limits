module

public import Freezing2.Companion.ReverseForest

/-!
# Coalescence in an actual reverse-forest transition

Two distinct components merge precisely when their roots are the selected pair,
in either order. The one-step hazard is consequently derived from the concrete
uniform ordered-pair law. Vertex presence and existing connectivity persist
under every supported reverse transition.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Classical

namespace Freezing2.ForestCoalescence

open Freezing1

variable {V : Type*} [DecidableEq V]

/-- Reverse growth keeps every existing vertex and never separates components. -/
def Coarsens (F G : RootedForest V) : Prop :=
  F.vertices ⊆ G.vertices ∧
    ∀ u ∈ F.vertices, ∀ v ∈ F.vertices, F.root u = F.root v → G.root u = G.root v

theorem Coarsens.refl (F : RootedForest V) : Coarsens F F :=
  ⟨Finset.Subset.refl _, fun _ _ _ _ h ↦ h⟩

theorem Coarsens.trans {F G H : RootedForest V} (hFG : Coarsens F G)
    (hGH : Coarsens G H) : Coarsens F H :=
  ⟨Finset.Subset.trans hFG.1 hGH.1,
    fun u hu v hv h ↦ hGH.2 u (hFG.1 hu) v (hFG.1 hv) (hFG.2 u hu v hv h)⟩

/-- A valid join coalesces two previously different roots exactly in the two
orders corresponding to their unordered pair. -/
theorem join_root_eq_iff (F : RootedForest V) {a b u v : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b)
    (huv : F.root u ≠ F.root v) :
    (F.join a b ha hb hab).root u = (F.join a b ha hb hab).root v ↔
      (a, b) = (F.root u, F.root v) ∨ (a, b) = (F.root v, F.root u) := by
  simp only [RootedForest.join, Prod.mk.injEq]
  by_cases hu : F.root u = b <;> by_cases hv : F.root v = b <;>
    simp_all <;> aesop

/-- Existing connectivity is preserved even for an invalid (identity) choice. -/
theorem joinChoice_coarsens (F : RootedForest V) (p : V × V) :
    Coarsens F (F.joinChoice p) := by
  unfold RootedForest.joinChoice
  split_ifs with hp
  · constructor
    · exact Finset.Subset.refl _
    · intro u hu v hv huv
      simp only [RootedForest.join, huv]
  · exact Coarsens.refl F

theorem joinChoice_root_eq_iff (F : RootedForest V) {p : V × V}
    (hp : p ∈ F.roots.offDiag) {u v : V} (huv : F.root u ≠ F.root v) :
    (F.joinChoice p).root u = (F.joinChoice p).root v ↔
      p = (F.root u, F.root v) ∨ p = (F.root v, F.root u) := by
  simp only [RootedForest.joinChoice, dite_eq_left hp]
  exact join_root_eq_iff F _ _ _ huv

/-- Inserting an isolated vertex changes no root of an existing vertex. -/
theorem adjoin_root_old (F : RootedForest V) {w u : V}
    (hw : w ∉ F.vertices) (hu : u ∈ F.vertices) :
    (F.adjoin w hw).root u = F.root u := by
  have hne : u ≠ w := fun h ↦ hw (h ▸ hu)
  simp [RootedForest.adjoin, hne]

/-- A newly inserted singleton is in a different component from every old vertex. -/
theorem adjoin_root_new_ne_old (F : RootedForest V) {w u : V}
    (hw : w ∉ F.vertices) (hu : u ∈ F.vertices) :
    (F.adjoin w hw).root w ≠ (F.adjoin w hw).root u := by
  rw [adjoin_root_old F hw hu]
  have hne : w ≠ F.root u := by
    intro heq
    exact hw (heq.symm ▸ F.root_mem u hu)
  simpa [RootedForest.adjoin] using hne

theorem adjoin_coarsens (F : RootedForest V) {w : V} (hw : w ∉ F.vertices) :
    Coarsens F (F.adjoin w hw) := by
  constructor
  · exact Finset.subset_insert _ _
  · intro u hu v hv huv
    simpa only [adjoin_root_old F hw hu, adjoin_root_old F hw hv] using huv

/-- Root equality is actual graph connectivity for present vertices. -/
theorem root_eq_iff_reachable (F : RootedForest V) {u v : V}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) :
    F.root u = F.root v ↔ F.graph.Reachable u v := by
  constructor
  · intro h
    obtain ⟨pu, _⟩ := F.exists_root_walk hu
    obtain ⟨pv, _⟩ := F.exists_root_walk hv
    have hu' : F.graph.Reachable u (F.root u) := pu.reachable.symm
    rw [h] at hu'
    exact hu'.trans pv.reachable
  · rintro ⟨p⟩
    exact F.root_eq_of_walk p

theorem Coarsens.reachable {F G : RootedForest V} (hFG : Coarsens F G)
    {u v : V} (hu : u ∈ F.vertices) (hv : v ∈ F.vertices)
    (h : F.graph.Reachable u v) : G.graph.Reachable u v :=
  (root_eq_iff_reachable G (hFG.1 hu) (hFG.1 hv)).mp
    (hFG.2 u hu v hv ((root_eq_iff_reachable F hu hv).mpr h))

variable [Countable V]

/-- The persistence event is measurable on a pair of forests. This follows
from countably many coordinate predicates; no discreteness of the product
sigma-algebra on the function-valued forest state space is assumed. -/
theorem measurable_coarsens :
    Measurable (fun p : RootedForest V × RootedForest V ↦ Coarsens p.1 p.2) := by
  have hm (u : V) : Measurable (fun F : RootedForest V ↦ u ∈ F.vertices) :=
    measurable_from_top
  have hr (u v : V) : Measurable (fun F : RootedForest V ↦ F.root u = F.root v) :=
    measurable_from_top
  change Measurable (fun p : RootedForest V × RootedForest V ↦
    (∀ u, u ∈ p.1.vertices → u ∈ p.2.vertices) ∧
      ∀ u, u ∈ p.1.vertices → ∀ v, v ∈ p.1.vertices →
        p.1.root u = p.1.root v → p.2.root u = p.2.root v)
  exact (Measurable.forall fun u ↦
    ((hm u).comp measurable_fst).imp ((hm u).comp measurable_snd)).and
    (Measurable.forall fun u ↦ ((hm u).comp measurable_fst).imp
      (Measurable.forall fun v ↦ ((hm v).comp measurable_fst).imp
        (((hr u v).comp measurable_fst).imp ((hr u v).comp measurable_snd))))

theorem measurableSet_coarsens :
    MeasurableSet {p : RootedForest V × RootedForest V | Coarsens p.1 p.2} :=
  measurable_coarsens.setOf

variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- Exact probability of first coalescence in the concrete join law. -/
theorem joinLaw_coalescence (F : RootedForest V) (hF : 2 ≤ F.roots.card)
    {u v : V} (hu : u ∈ F.vertices) (hv : v ∈ F.vertices)
    (huv : F.root u ≠ F.root v) :
    F.joinLaw.real {G | G.root u = G.root v} =
      2 / ((F.roots.card : ℝ) * ((F.roots.card : ℝ) - 1)) := by
  have hf : F.roots.offDiag.filter (fun p ↦ (F.joinChoice p).root u =
      (F.joinChoice p).root v) = F.roots.offDiag.filter
      (fun p ↦ p = (F.root u, F.root v) ∨ p = (F.root v, F.root u)) := by
    apply Finset.filter_congr
    intro p hp
    exact joinChoice_root_eq_iff F hp huv
  change (F.joinLaw {G | G.root u = G.root v}).toReal = _
  rw [RootedForest.joinLaw_apply F hF]
  simp only [Set.mem_ofPred_eq]
  rw [hf]
  have h := uniformRootPair_unordered F.roots (F.root_mem_roots hu)
    (F.root_mem_roots hv) huv
  simpa only [uniformRootPair, Measure.real, Measure.uniformOfFinset_apply,
    Set.mem_ofPred_eq] using h

/-- All existing vertices and all existing component equalities survive a join. -/
theorem joinLaw_ae_coarsens (F : RootedForest V) :
    ∀ᵐ G ∂F.joinLaw, Coarsens F G := by
  by_cases hF : 2 ≤ F.roots.card
  · exact F.joinLaw_ae hF _ (fun p _ ↦ joinChoice_coarsens F p)
  · simp only [RootedForest.joinLaw, ite_eq_right hF]
    exact (ae_dirac_iff (by trivial)).mpr (Coarsens.refl F)

/-- The deterministic freezing transition leaves old component representatives unchanged. -/
theorem insertLabel_root_old (F : Reverse.Forest) (i : ℕ) {u : ℕ ⊕ ℕ}
    (hu : u ∈ F.vertices) : (Reverse.insertLabel F i).root u = F.root u := by
  unfold Reverse.insertLabel
  split_ifs with h
  · rfl
  · exact adjoin_root_old F h hu

theorem insertLabel_coarsens (F : Reverse.Forest) (i : ℕ) :
    Coarsens F (Reverse.insertLabel F i) := by
  unfold Reverse.insertLabel
  split_ifs with h
  · exact Coarsens.refl F
  · exact adjoin_coarsens F h

/-- The freezing label starts in a new component whenever it is fresh. -/
theorem insertLabel_root_new_ne_old (F : Reverse.Forest) (i : ℕ)
    (hi : Sum.inr i ∉ F.vertices) {u : ℕ ⊕ ℕ} (hu : u ∈ F.vertices) :
    (Reverse.insertLabel F i).root (.inr i) ≠ (Reverse.insertLabel F i).root u := by
  simp only [Reverse.insertLabel, dite_eq_right hi]
  exact adjoin_root_new_ne_old F hi hu

/-- Membership and connectivity persist almost surely without any legality
hypothesis; the totalized fallback transitions have the same property. -/
theorem transitionLaw_ae_coarsens (x : SignSequence) (i : ℕ) (F : Reverse.Forest) :
    ∀ᵐ G ∂Reverse.transitionLaw x i F, Coarsens F G := by
  cases hx : x (i + 1)
  · simp only [Reverse.transitionLaw, hx, Bool.false_eq_true, ↓reduceIte]
    exact (ae_dirac_iff (by trivial)).mpr (insertLabel_coarsens F i)
  · simp only [Reverse.transitionLaw, hx, ↓reduceIte]
    exact joinLaw_ae_coarsens F

/-- In particular, the two vertices stay present and an existing connection
cannot be lost in the reverse construction. -/
theorem transitionLaw_ae_connected (x : SignSequence) (i : ℕ) (F : Reverse.Forest)
    {u v : ℕ ⊕ ℕ} (hu : u ∈ F.vertices) (hv : v ∈ F.vertices)
    (huv : F.root u = F.root v) :
    ∀ᵐ G ∂Reverse.transitionLaw x i F,
      u ∈ G.vertices ∧ v ∈ G.vertices ∧ G.root u = G.root v := by
  filter_upwards [transitionLaw_ae_coarsens x i F] with G hG
  exact ⟨hG.1 hu, hG.1 hv, hG.2 u hu v hv huv⟩

theorem transitionLaw_connected_probability_one (x : SignSequence) (i : ℕ)
    (F : Reverse.Forest) {u v : ℕ ⊕ ℕ} (hu : u ∈ F.vertices) (hv : v ∈ F.vertices)
    (huv : F.root u = F.root v) :
    (Reverse.transitionLaw x i F).real {G | G.root u = G.root v} = 1 := by
  have h : ∀ᵐ G ∂Reverse.transitionLaw x i F, G.root u = G.root v :=
    (transitionLaw_ae_connected x i F hu hv huv).mono fun _ hG ↦ hG.2.2
  change ((Reverse.transitionLaw x i F) {G | G.root u = G.root v}).toReal = 1
  rw [(ae_iff_prob_eq_one measurable_from_top).mp h]
  simp

/-- The source's one-step hazard, with the population before the reverse merge
and the original sign determining whether a merge is attempted. -/
theorem transitionLaw_coalescence {x : SignSequence} {n i : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : Reverse.ValidAt x n (i + 1) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (huv : F.root u ≠ F.root v) :
    (Reverse.transitionLaw x i F).real {G | G.root u = G.root v} =
      if x (i + 1) then
        2 / ((activeCount x (i + 1) : ℝ) * ((activeCount x (i + 1) : ℝ) - 1))
      else 0 := by
  have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
    le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast (Nat.succ_le_of_lt hi)) hn
  cases hx : x (i + 1)
  · simp [Reverse.transitionLaw, hx, Measure.real,
      insertLabel_root_old F i hu, insertLabel_root_old F i hv, huv]
  · have htwo : 2 ≤ F.roots.card := by
      rw [hF.roots_card]
      exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
    have hc : ((activeCount x (i + 1)).toNat : ℝ) = (activeCount x (i + 1) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (activeCount_nonneg_of_le_extinctionTime hiτ)
    simp only [Reverse.transitionLaw, hx, ↓reduceIte]
    rw [joinLaw_coalescence F htwo hu hv huv, hF.roots_card, hc]

/-- Uniformly covers states whose two vertices have already coalesced and states
whose roots remain distinct. This is suitable for conditional-kernel recursion. -/
theorem transitionLaw_root_eq_probability {x : SignSequence} {n i : ℕ}
    {F : Reverse.Forest} (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : Reverse.ValidAt x n (i + 1) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) :
    (Reverse.transitionLaw x i F).real {G | G.root u = G.root v} =
      if F.root u = F.root v then 1 else
      if x (i + 1) then
        2 / ((activeCount x (i + 1) : ℝ) * ((activeCount x (i + 1) : ℝ) - 1))
      else 0 := by
  by_cases huv : F.root u = F.root v
  · rw [ite_eq_left huv, transitionLaw_connected_probability_one x i F hu hv huv]
  · rw [ite_eq_right huv, transitionLaw_coalescence hn hi hF hu hv huv]

/-- The survival factor for two still distinct components follows from the
exact merger probability, rather than an independently assumed hazard law. -/
theorem transitionLaw_noncoalescence {x : SignSequence} {n i : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : Reverse.ValidAt x n (i + 1) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (huv : F.root u ≠ F.root v) :
    (Reverse.transitionLaw x i F).real {G | G.root u ≠ G.root v} =
      1 - if x (i + 1) then
        2 / ((activeCount x (i + 1) : ℝ) * ((activeCount x (i + 1) : ℝ) - 1))
      else 0 := by
  change (Reverse.transitionLaw x i F).real {G | G.root u = G.root v}ᶜ = _
  rw [probReal_compl_eq_one_sub (by trivial), transitionLaw_coalescence hn hi hF hu hv huv]

end Freezing2.ForestCoalescence
