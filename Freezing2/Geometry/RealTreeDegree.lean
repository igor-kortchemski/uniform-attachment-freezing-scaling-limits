module

public import Freezing2.Geometry.RealTree

/-!
# Degrees and leaves of real trees

The degree of a point `x` of a metric space is the number (in `ℕ∞`) of connected
components of `X \ {x}`; a leaf is a point of degree one. In a real tree, a point
whose complement has at least two components lies strictly inside a geodesic
segment between two other points.
-/

@[expose] public section

open Set Topology Metric

namespace Freezing2.RealTree

variable {X : Type*} [MetricSpace X]

/-- The connected components of `X \ {x}`. -/
def complementComponents (x : X) : Set (Set X) :=
  {C | ∃ y, y ≠ x ∧ C = connectedComponentIn {x}ᶜ y}

/-- The degree of `x`: the number of connected components of `X \ {x}`. -/
noncomputable def degree (x : X) : ℕ∞ := (complementComponents x).encard

/-- A leaf is a point of degree one (Evans' convention). In a space with at least two
points this means that `X \ {x}` is connected; a one-point space has no leaves. -/
def IsLeaf (x : X) : Prop := degree x = 1

theorem degree_eq_zero_iff (x : X) : degree x = 0 ↔ ∀ y : X, y = x := by
  unfold degree complementComponents
  rw [encard_eq_zero, eq_empty_iff_forall_notMem]
  constructor
  · intro h y
    by_contra hy
    exact h _ ⟨y, hy, rfl⟩
  · rintro h C ⟨y, hy, rfl⟩
    exact hy (h y)

/-- If two points `y, z ≠ x` lie in different components of `X \ {x}`, every segment
from `y` to `z` passes through `x`. -/
theorem mem_segment_of_ne_component {x y z : X} (hy : y ≠ x) (hz : z ≠ x)
    (hyz : connectedComponentIn {x}ᶜ y ≠ connectedComponentIn {x}ᶜ z) {γ : ℝ → X}
    (hγ : IsSegment y z γ) : dist y x + dist x z = dist y z := by
  have hcont : ContinuousOn γ (Icc 0 (dist y z)) := by
    refine Metric.continuousOn_iff.mpr fun a ha ε hε ↦ ⟨ε, hε, fun b hb hab ↦ ?_⟩
    rw [hγ.2.2 b hb a ha, ← Real.dist_eq]
    exact hab
  by_contra hne
  have hx : x ∉ γ '' Icc 0 (dist y z) := by
    rintro ⟨a, ha, rfl⟩
    apply hne
    rw [hγ.dist_left ha, hγ.dist_right ha]
    ring
  have hconn : IsPreconnected (γ '' Icc 0 (dist y z)) := isPreconnected_Icc.image γ hcont
  have hsub : γ '' Icc 0 (dist y z) ⊆ {x}ᶜ := fun p hp hpx ↦ hx (hpx ▸ hp)
  have hy' : y ∈ γ '' Icc 0 (dist y z) := ⟨0, left_mem_Icc.mpr dist_nonneg, hγ.1⟩
  have hz' : z ∈ γ '' Icc 0 (dist y z) := ⟨dist y z, right_mem_Icc.mpr dist_nonneg, hγ.2.1⟩
  have h1 := hconn.subset_connectedComponentIn hy' hsub
  exact hyz (connectedComponentIn_eq (h1 hz'))

/-- **Non-leaves of real trees.** In a real tree, a point of degree at least two lies
strictly between two other points. -/
theorem exists_between_of_two_le_degree (hT : IsRealTree X) {x : X} (hx : 2 ≤ degree x) :
    ∃ y z, y ≠ x ∧ z ≠ x ∧ dist y x + dist x z = dist y z := by
  obtain ⟨C₁, ⟨y, hy, rfl⟩, C₂, ⟨z, hz, rfl⟩, hne⟩ :=
    (one_lt_encard_iff_nontrivial.mp (lt_of_lt_of_le (by norm_num) hx))
  obtain ⟨γ, hγ⟩ := (hT y z).1
  exact ⟨y, z, hy, hz, mem_segment_of_ne_component hy hz hne hγ⟩

end Freezing2.RealTree
