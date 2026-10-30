module

public import Freezing2.Companion.MainMaximum
public import Freezing2.Analysis.HarmonicAsymptotics

/-!
# The actual attachment/freezing tree law

The vendored companion construction uses Boolean signs, whereas this project
uses integer signs. These lemmas identify their walks, survival conditions and
height scales exactly. The tree law is the iterated uniform-active-vertex law
of Algorithm 1, and its maintained heights equal distances in the finite tree.
No equality with the reverse construction is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Freezing2

/-- Encode an integer signed schedule for the companion's Algorithm 1. -/
def companionSchedule (x : ℕ → ℤ) : Freezing1.SignSequence := fun i ↦ decide (x i = 1)

theorem companionSchedule_value (x : ℕ → ℤ) (hx : IsSigned x) {i : ℕ} (hi : 0 < i) :
    (if companionSchedule x i then (1 : ℤ) else -1) = x i := by
  rcases hx i hi with h | h <;> simp [companionSchedule, h]

/-- The two schedule encodings have identical integer populations. -/
theorem companion_activeCount (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ) :
    Freezing1.activeCount (companionSchedule x) n = activeCount x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Freezing1.activeCount_succ, activeCount_succ, ih,
      companionSchedule_value x hx (by omega : 0 < n + 1)]

theorem companion_positiveThrough (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) : Freezing1.PositiveThrough (companionSchedule x) n := by
  intro i hi
  rw [companion_activeCount x hx]
  exact hs i hi

/-- The companion's stopping-time premise follows from the source survival premise. -/
theorem companion_before_extinction (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) :
    (n : ℕ∞) < Freezing1.extinctionTime (companionSchedule x) :=
  (Freezing1.lt_extinctionTime_iff _ _).mpr (companion_positiveThrough x hx hs)

/-- Exact equality of the companion height scale and the paper's up-step harmonic sum. -/
theorem companion_heightScale (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ) :
    Freezing1.heightScale (companionSchedule x) n = harmonicUpInterval x 0 n := by
  unfold Freezing1.heightScale harmonicUpInterval
  apply Finset.sum_congr rfl
  intro i _
  simp [companionSchedule, companion_activeCount x hx, one_div]

/-- Algorithm 1's random tree for the original integer-sign triangular array. -/
noncomputable def freezingTreeLaw (x : ℕ → ℕ → ℤ) (n : ℕ) :
    Measure Freezing1.Forward.State :=
  Freezing1.Forward.treeLaw (companionSchedule (x n)) n

instance freezingTreeLaw_probability (x : ℕ → ℕ → ℤ) (n : ℕ) :
    IsProbabilityMeasure (freezingTreeLaw x n) := by
  unfold freezingTreeLaw
  infer_instance

/-- The constructed law is supported on valid finite rooted tree states. -/
theorem freezingTreeLaw_valid (x : ℕ → ℕ → ℤ) (n : ℕ) :
    ∀ᵐ s ∂freezingTreeLaw x n, Freezing1.Forward.ValidAt n s :=
  Freezing1.Forward.treeLaw_valid _ _

/-- The maximum used in the height theorem is the actual maximum root distance
in the finite tree, rather than a separate uncharacterized statistic. -/
theorem treeHeight_le_iff_graph_distance {n : ℕ} {s : Freezing1.Forward.State}
    (hs : Freezing1.Forward.ValidAt n s) (h : ℕ) :
    Freezing1.Forward.treeHeight s ≤ h ↔
      ∀ v : {v // v ∈ s.vertices}, s.tree.dist ⟨0, hs.root_mem⟩ v ≤ h := by
  rw [Freezing1.Forward.treeHeight, Finset.sup_le_iff]
  constructor
  · intro hle v
    rw [← hs.height_eq_tree_dist v]
    exact hle v v.property
  · intro hle v hv
    simpa only [← hs.height_eq_tree_dist ⟨v, hv⟩] using hle ⟨v, hv⟩

end Freezing2
