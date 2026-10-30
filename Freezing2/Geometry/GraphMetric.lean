module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Topology.MetricSpace.GromovHausdorff

/-!
# Finite graph distances as compact metric spaces

A connected graph with positive distance scaling defines a genuine metric.
For a finite vertex set this supplies a compact metric space and its actual
point in Mathlib's Gromov--Hausdorff space. No graph-limit claim is assumed.
-/

@[expose] public section

open GromovHausdorff
open scoped Topology

namespace Freezing2

/-- The positively scaled graph distance, with its induced metric topology. -/
@[instance_reducible] noncomputable def scaledGraphMetric {V : Type*} (G : SimpleGraph V)
    (hG : G.Connected) (c : ℝ) (hc : 0 < c) : MetricSpace V where
  dist u v := c * (G.dist u v : ℝ)
  dist_self u := by simp
  dist_comm u v := by rw [SimpleGraph.dist_comm]
  dist_triangle u v w := by
    have h : (G.dist u w : ℝ) ≤ (G.dist u v : ℝ) + (G.dist v w : ℝ) := by
      exact_mod_cast hG.dist_triangle (u := u) (v := v) (w := w)
    simpa only [mul_add] using mul_le_mul_of_nonneg_left h hc.le
  eq_of_dist_eq_zero := by
    intro u v h
    have hz : (G.dist u v : ℝ) = 0 := (mul_eq_zero.mp h).resolve_left hc.ne'
    exact hG.dist_eq_zero_iff.mp (by exact_mod_cast hz)

/-- A finite connected graph is represented by its true scaled metric in
the space of isometry classes of nonempty compact metric spaces. -/
noncomputable def scaledGraphGHSpace {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : G.Connected) (c : ℝ) (hc : 0 < c) : GHSpace := by
  letI := scaledGraphMetric G hG c hc
  letI := hG.nonempty
  exact toGHSpace V

/-- A map with uniformly bounded distance distortion and dense image gives
the standard Gromov--Hausdorff bound for this actual graph metric. -/
theorem scaledGraph_ghDist_le {V Y : Type*} [Finite V]
    (G : SimpleGraph V) (hG : G.Connected) (c : ℝ) (hc : 0 < c)
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] (f : V → Y) {D r : ℝ}
    (hdense : ∀ y : Y, ∃ v : V, dist y (f v) ≤ r)
    (herror : ∀ u v, |c * (G.dist u v : ℝ) - dist (f u) (f v)| ≤ D) :
    letI := scaledGraphMetric G hG c hc
    letI := hG.nonempty
    ghDist V Y ≤ D / 2 + r := by
  let := scaledGraphMetric G hG c hc
  let := hG.nonempty
  have h := ghDist_le_of_approx_subsets (s := Set.univ) (fun v : (Set.univ : Set V) ↦ f v.val)
    (ε₁ := 0) (ε₂ := D) (ε₃ := r)
    (fun v ↦ ⟨v, Set.mem_univ _, by simp⟩)
    (fun y ↦ by obtain ⟨v, hv⟩ := hdense y; exact ⟨⟨v, Set.mem_univ _⟩, hv⟩)
    (fun u v ↦ herror u.val v.val)
  simpa only [zero_add] using h

end Freezing2
