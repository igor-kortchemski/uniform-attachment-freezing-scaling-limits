module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.ReverseForest

/-!
# Reverse forests with the actual edge creation times

Algorithm 2 labels each newly merged edge by its reverse step index. The
existing graph-valued reverse law omits this information. This module lifts
the same uniform ordered-root-pair kernels to timestamped forests and proves
that forgetting timestamps gives exactly the existing reverse law.

The timestamp is stored at the child endpoint of each parent edge. Zero is
reserved for roots. No forward/reverse equality in law is assumed here.
-/

@[expose] public section

namespace Freezing1.ReverseStamped

open MeasureTheory
open scoped ENNReal Classical

structure Forest where
  forest : Reverse.Forest
  edgeTime : (ℕ ⊕ ℕ) → ℕ

instance : MeasurableSpace Forest := ⊤
instance : DiscreteMeasurableSpace Forest := ⟨fun _ => trivial⟩

/-- The initial active vertices carry no parent edges. -/
def initial (x : SignSequence) (n : ℕ) : Forest :=
  ⟨Reverse.initial x n, fun _ => 0⟩

/-- Merge the chosen roots, storing the time on the second root's new
parent edge. The invalid-choice fallback matches the existing kernel. -/
def joinChoice (F : Forest) (t : ℕ) (p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) : Forest :=
  if h : p ∈ F.forest.roots.offDiag then
    ⟨F.forest.join p.1 p.2 (Finset.mem_offDiag.mp h).1
      (Finset.mem_offDiag.mp h).2.1 (Finset.mem_offDiag.mp h).2.2,
      Function.update F.edgeTime p.2 t⟩
  else F

@[simp] theorem joinChoice_forest (F : Forest) (t : ℕ) (p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) :
    (joinChoice F t p).forest = F.forest.joinChoice p := by
  unfold joinChoice RootedForest.joinChoice
  split_ifs <;> rfl

theorem joinChoice_edgeTime (F : Forest) (t : ℕ) {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)}
    (hp : p ∈ F.forest.roots.offDiag) :
    (joinChoice F t p).edgeTime = Function.update F.edgeTime p.2 t := by
  simp only [joinChoice, dite_eq_left hp]

/-- Insert the prescribed freezing label as a new root, with no parent edge. -/
def insertLabel (F : Forest) (i : ℕ) : Forest :=
  if h : Sum.inr i ∈ F.forest.vertices then F
  else ⟨F.forest.adjoin (.inr i) h, Function.update F.edgeTime (.inr i) 0⟩

@[simp] theorem insertLabel_forest (F : Forest) (i : ℕ) :
    (insertLabel F i).forest = Reverse.insertLabel F.forest i := by
  unfold insertLabel Reverse.insertLabel
  split_ifs <;> rfl

noncomputable def joinLaw (F : Forest) (t : ℕ) : Measure Forest :=
  if 2 ≤ F.forest.roots.card then
    (uniformRootPair F.forest.roots).map (joinChoice F t)
  else Measure.dirac F

instance joinLaw_probability (F : Forest) (t : ℕ) : IsProbabilityMeasure (joinLaw F t) := by
  unfold joinLaw
  split_ifs with h
  · have := uniformRootPair_isProbabilityMeasure F.forest.roots h
    have hm : Measurable (joinChoice F t) := measurable_of_countable _
    exact Measure.isProbabilityMeasure_map_iff hm.aemeasurable |>.mpr inferInstance
  · infer_instance

/-- Timestamp recording does not change the underlying root-pair kernel. -/
theorem map_joinLaw (F : Forest) (t : ℕ) :
    (joinLaw F t).map Forest.forest = F.forest.joinLaw := by
  unfold joinLaw RootedForest.joinLaw
  split_ifs
  · rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
    congr 1
    funext p
    exact joinChoice_forest F t p
  · exact Measure.map_dirac' measurable_from_top _

/-- The same sign-controlled transition as Algorithm 2, retaining edge times. -/
noncomputable def transitionLaw (x : SignSequence) (i : ℕ) (F : Forest) : Measure Forest :=
  if x (i + 1) then joinLaw F (i + 1) else Measure.dirac (insertLabel F i)

instance transitionLaw_probability (x : SignSequence) (i : ℕ) (F : Forest) :
    IsProbabilityMeasure (transitionLaw x i F) := by
  unfold transitionLaw
  split_ifs <;> infer_instance

/-- Exact projection of the lifted transition onto the already defined kernel. -/
theorem map_transitionLaw (x : SignSequence) (i : ℕ) (F : Forest) :
    (transitionLaw x i F).map Forest.forest = Reverse.transitionLaw x i F.forest := by
  unfold transitionLaw Reverse.transitionLaw
  split_ifs
  · exact map_joinLaw F (i + 1)
  · rw [Measure.map_dirac' measurable_from_top, insertLabel_forest]

noncomputable def lawAfter (x : SignSequence) (n : ℕ) : ℕ → Measure Forest
  | 0 => Measure.dirac (initial x n)
  | k + 1 => if k < n then
      (lawAfter x n k).bind (transitionLaw x (n - (k + 1)))
    else lawAfter x n k

instance lawAfter_probability (x : SignSequence) (n k : ℕ) :
    IsProbabilityMeasure (lawAfter x n k) := by
  induction k with
  | zero => change IsProbabilityMeasure (Measure.dirac (initial x n)); infer_instance
  | succ k ih =>
    simp only [lawAfter]
    split_ifs
    · exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
        (Filter.Eventually.of_forall (fun F => transitionLaw_probability x _ F))
    · exact ih

/-- At every reverse phase, forgetting edge times gives precisely the original
graph-valued law. This includes absorption endpoints and the held terminal law. -/
theorem map_lawAfter (x : SignSequence) (n k : ℕ) :
    (lawAfter x n k).map Forest.forest = Reverse.lawAfter x n k := by
  induction k with
  | zero => exact Measure.map_dirac' measurable_from_top _
  | succ k ih =>
    simp only [lawAfter, Reverse.lawAfter]
    split_ifs with hk
    · rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
      calc
        _ = (lawAfter x n k).bind (fun F => Reverse.transitionLaw x (n - (k + 1)) F.forest) := by
          congr 1
          funext F
          exact map_transitionLaw x (n - (k + 1)) F
        _ = ((lawAfter x n k).map Forest.forest).bind
            (Reverse.transitionLaw x (n - (k + 1))) :=
          (Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable).symm
        _ = _ := by rw [ih]
    · exact ih

noncomputable def treeLaw (x : SignSequence) (n : ℕ) : Measure Forest := lawAfter x n n

instance treeLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (treeLaw x n) := lawAfter_probability x n n

theorem map_treeLaw (x : SignSequence) (n : ℕ) :
    (treeLaw x n).map Forest.forest = Reverse.treeLaw x n := map_lawAfter x n n

/-- The projected forest retains all proved label, root-count, and acyclicity
invariants through the extinction endpoint. -/
theorem lawAfter_forest_valid (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k ≤ n) :
    ∀ᵐ F ∂lawAfter x n k, Reverse.ValidAt x n (n - k) F.forest := by
  apply ae_of_ae_map (f := Forest.forest) measurable_from_top.aemeasurable
  rw [map_lawAfter]
  exact Reverse.lawAfter_valid x n k hn hk

/-- The timestamped terminal object projects to a genuine finite rooted tree. -/
theorem treeLaw_forest_isTree (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂treeLaw x n, F.forest.toGraph.IsTree := by
  apply ae_of_ae_map (f := Forest.forest)
    (p := fun G : Reverse.Forest => G.toGraph.IsTree) measurable_from_top.aemeasurable
  rw [map_treeLaw]
  exact Reverse.treeLaw_isTree x n hn

end Freezing1.ReverseStamped
