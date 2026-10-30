module

public import Freezing2.Geometry.GraphMetric
public import Freezing2.Companion.RootedForest

/-!
# The Gromov--Hausdorff point of a finite rooted forest

On connected forests with positive scaling, this is the isometry class of
the actual scaled graph metric. A singleton value makes the function total
outside that domain; applications must prove the domain condition almost surely.
-/

@[expose] public section

open GromovHausdorff
open scoped Classical

namespace Freezing2

noncomputable def forestScaledGHSpace {V : Type*} [DecidableEq V]
    (F : Freezing1.RootedForest V) (c : ℝ) : GHSpace :=
  if h : F.toGraph.Connected ∧ 0 < c then
    scaledGraphGHSpace F.toGraph h.1 c h.2
  else toGHSpace Unit

theorem forestScaledGHSpace_eq {V : Type*} [DecidableEq V]
    (F : Freezing1.RootedForest V) (c : ℝ) (hF : F.toGraph.Connected) (hc : 0 < c) :
    forestScaledGHSpace F c = scaledGraphGHSpace F.toGraph hF c hc := by
  simp only [forestScaledGHSpace, dite_eq_left (show F.toGraph.Connected ∧ 0 < c from ⟨hF, hc⟩)]

/-- The concrete forest representation has the same standard GH error bound
as its actual finite graph, with no assumed limit theorem. -/
theorem forestScaledGHSpace_dist_le {V Y : Type*} [DecidableEq V]
    (F : Freezing1.RootedForest V) (c : ℝ) (hF : F.toGraph.Connected) (hc : 0 < c)
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (f : {v // v ∈ F.vertices} → Y) {D r : ℝ}
    (hdense : ∀ y : Y, ∃ v, dist y (f v) ≤ r)
    (herror : ∀ u v, |c * (F.toGraph.dist u v : ℝ) - dist (f u) (f v)| ≤ D) :
    dist (forestScaledGHSpace F c) (toGHSpace Y) ≤ D / 2 + r := by
  rw [forestScaledGHSpace_eq F c hF hc]
  exact scaledGraph_ghDist_le F.toGraph hF c hc f hdense herror

end Freezing2
