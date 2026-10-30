module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.RootedForest
public import Freezing2.Companion.UniformRootPair
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The uniform root-merging kernel

This is the actual one-step probability kernel of Algorithm 2. Its inputs are
rooted forests, and its output is obtained by sampling an ordered pair of
distinct roots. The identity transition on inputs with fewer than two roots
totalizes the kernel; legal attachment steps are proved to have at least two
roots when the kernel is used by the reverse process.
-/

@[expose] public section

namespace Freezing1.RootedForest

open MeasureTheory
open scoped ENNReal Classical

variable {V : Type*} [DecidableEq V]

instance : MeasurableSpace (RootedForest V) := ⊤
instance : DiscreteMeasurableSpace (RootedForest V) := ⟨fun _ => trivial⟩

/-- Execute a valid ordered-pair choice. The other branch is outside the
support of the uniform choice and is never used on a legal merge. -/
def joinChoice (F : RootedForest V) (p : V × V) : RootedForest V :=
  if h : p ∈ F.roots.offDiag then
    F.join p.1 p.2 (Finset.mem_offDiag.mp h).1 (Finset.mem_offDiag.mp h).2.1
      (Finset.mem_offDiag.mp h).2.2
  else F

theorem joinChoice_depth (F : RootedForest V) {p : V × V}
    (hp : p ∈ F.roots.offDiag) (v : V) :
    (F.joinChoice p).depth v = F.depth v + if F.root v = p.2 then 1 else 0 := by
  simp [joinChoice, hp, join_depth]

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- Uniformly merge two different components; inputs with fewer than two
components remain unchanged. -/
noncomputable def joinLaw (F : RootedForest V) : Measure (RootedForest V) :=
  if 2 ≤ F.roots.card then (uniformRootPair F.roots).map F.joinChoice else Measure.dirac F

instance joinLaw_probability (F : RootedForest V) : IsProbabilityMeasure F.joinLaw := by
  unfold joinLaw
  split_ifs with h
  · have := uniformRootPair_isProbabilityMeasure F.roots h
    have hm : Measurable F.joinChoice := measurable_of_countable _
    exact Measure.isProbabilityMeasure_map_iff hm.aemeasurable |>.mpr inferInstance
  · infer_instance

theorem joinLaw_apply (F : RootedForest V) (hF : 2 ≤ F.roots.card)
    (A : Set (RootedForest V)) :
    F.joinLaw A = ((F.roots.offDiag.filter fun p => F.joinChoice p ∈ A).card : ℝ≥0∞) /
      F.roots.offDiag.card := by
  have hm : Measurable F.joinChoice := measurable_of_countable _
  rw [joinLaw, ite_eq_left hF, Measure.map_apply hm (by trivial),
    uniformRootPair, Measure.uniformOfFinset_apply]
  rfl

theorem joinLaw_ae (F : RootedForest V) (hF : 2 ≤ F.roots.card)
    (P : RootedForest V → Prop)
    (hP : ∀ p ∈ F.roots.offDiag, P (F.joinChoice p)) : ∀ᵐ F' ∂F.joinLaw, P F' := by
  apply (ae_iff_prob_eq_one measurable_from_top).mpr
  rw [joinLaw_apply F hF]
  have hf : F.roots.offDiag.filter (fun p => F.joinChoice p ∈ {F' | P F'}) =
      F.roots.offDiag := Finset.filter_eq_self.mpr hP
  rw [hf]
  exact ENNReal.div_self
    (by exact_mod_cast (offDiag_nonempty_of_two_le_card hF).card_pos.ne')
    (ENNReal.natCast_ne_top _)

/-- Exact one-step height-increment probability for an existing vertex. -/
theorem joinLaw_depth_increment (F : RootedForest V) (hF : 2 ≤ F.roots.card)
    {v : V} (hv : v ∈ F.vertices) :
    F.joinLaw.real {F' | F'.depth v = F.depth v + 1} = 1 / (F.roots.card : ℝ) := by
  have hf : F.roots.offDiag.filter (fun p => (F.joinChoice p).depth v = F.depth v + 1) =
      F.roots.offDiag.filter (fun p => p.2 = F.root v) := by
    apply Finset.filter_congr
    intro p hp
    rw [joinChoice_depth F hp]
    by_cases h : F.root v = p.2
    · simp [h]
    · simp [h, Ne.symm h]
  change (F.joinLaw {F' | F'.depth v = F.depth v + 1}).toReal = _
  rw [joinLaw_apply F hF]
  simp only [Set.mem_ofPred_eq]
  rw [hf]
  have h := uniformRootPair_second F.roots (F.root_mem_roots hv) hF
  simpa only [uniformRootPair, Measure.real, Measure.uniformOfFinset_apply,
    Set.mem_ofPred_eq] using h

/-- The height increment is always zero or one; no other values are hidden
by the single-event probability formula. -/
theorem joinLaw_depth_support (F : RootedForest V) (hF : 2 ≤ F.roots.card) (v : V) :
    ∀ᵐ F' ∂F.joinLaw, F'.depth v = F.depth v ∨ F'.depth v = F.depth v + 1 := by
  apply F.joinLaw_ae hF
  intro p hp
  rw [joinChoice_depth F hp]
  split_ifs <;> simp

theorem joinLaw_vertices (F : RootedForest V) (hF : 2 ≤ F.roots.card) :
    ∀ᵐ F' ∂F.joinLaw, F'.vertices = F.vertices := by
  apply F.joinLaw_ae hF
  intro p hp
  simp [joinChoice, hp]

theorem joinLaw_roots_card (F : RootedForest V) (hF : 2 ≤ F.roots.card) :
    ∀ᵐ F' ∂F.joinLaw, F'.roots.card + 1 = F.roots.card := by
  apply F.joinLaw_ae hF
  intro p hp
  simp only [joinChoice, dite_eq_left hp]
  exact F.join_card_roots _ _ _

theorem joinLaw_isAcyclic (F : RootedForest V) (hF : 2 ≤ F.roots.card)
    (ha : F.graph.IsAcyclic) : ∀ᵐ F' ∂F.joinLaw, F'.graph.IsAcyclic := by
  apply F.joinLaw_ae hF
  intro p hp
  simp only [joinChoice, dite_eq_left hp]
  exact F.join_isAcyclic ha _ _ _

end Freezing1.RootedForest
