module

public import Freezing2.Probability.CanonicalForwardGraph
public import Freezing2.Probability.DistanceApproximation

/-!
# Exact root and metric transport under the canonical tree isomorphism

The finite graph isomorphism preserves graph distance. The ambient label and
birth-ID graphs have the same distances as their induced finite trees. The
actual reverse root is sent to the forward root identifier zero.
-/

@[expose] public section

namespace Freezing2

/-- A graph isomorphism preserves graph distance on a connected graph. -/
theorem graphIso_dist_eq {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B}
    (e : G ≃g H) (hG : G.Connected) (u v : A) : H.dist (e u) (e v) = G.dist u v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  have hr : H.Reachable (e u) (e v) := ⟨p.map e.toHom⟩
  obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
  apply le_antisymm
  · have hd := H.dist_le (p.map e.toHom)
    simpa [SimpleGraph.Walk.length_map, hp] using hd
  · have hd := G.dist_le (q.map e.symm.toHom)
    simpa [SimpleGraph.Walk.length_map, hq] using hd

theorem forward_walk_support_mem {n : ℕ} {s : Freezing1.Forward.State}
    (hs : Freezing1.Forward.ValidAt n s) {u v : ℕ} (p : s.graph.Walk u v)
    (hu : u ∈ s.vertices) : ∀ w ∈ p.support, w ∈ s.vertices := by
  induction p with
  | nil => simpa using hu
  | cons h p ih =>
    intro w hw
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hu
    · exact ih (hs.adj_mem h).2 w hw

/-- The ambient identifier type adds only isolated vertices; it does not
change the distances between actual forward vertices. -/
theorem forward_tree_dist_eq {n : ℕ} {s : Freezing1.Forward.State}
    (hs : Freezing1.Forward.ValidAt n s) (u v : {w // w ∈ s.vertices}) :
    s.tree.dist u v = s.graph.dist u.val v.val := by
  let e : s.tree →g s.graph := ⟨Subtype.val, fun {_ _} h ↦ h⟩
  have hr := (hs.reachable u.val u.property).symm.trans (hs.reachable v.val v.property)
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  let q : s.tree.Walk u v := p.induce (s.vertices : Set ℕ)
    (forward_walk_support_mem hs p u.property)
  have hq : q.length = p.length := walk_induce_length p _ _
  apply le_antisymm
  · exact (s.tree.dist_le q).trans_eq (hq.trans hp)
  · obtain ⟨r, hr⟩ := q.reachable.exists_walk_length_eq_dist
    have hd := s.graph.dist_le (r.map e)
    rw [SimpleGraph.Walk.length_map, hr] at hd
    exact hd

namespace ReverseStamped

/-- The distinguished actual root is sent to identifier zero, not to an
arbitrary sampled vertex. -/
theorem canonicalVertexEquiv_root_zero {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {r : ℕ ⊕ ℕ} (hr : r ∈ F.forest.roots) :
    canonicalVertexEquiv hF ht ho ⟨r, (Freezing1.RootedForest.mem_roots.mp hr).1⟩ =
      ⟨0, (ForwardHistory.state_valid x (canonicalHistory x n F)).root_mem⟩ := by
  apply Subtype.ext
  change F.edgeTime r = 0
  exact (ht.root_zero r (Freezing1.RootedForest.mem_roots.mp hr).1).mpr hr

/-- The canonical tree map preserves actual graph distances between all
present vertices, with no distinctness assumption. -/
theorem canonicalForwardState_graph_dist {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {u v : ℕ ⊕ ℕ} (hu : u ∈ F.forest.vertices) (hv : v ∈ F.forest.vertices) :
    (canonicalForwardState x n F).graph.dist (F.edgeTime u) (F.edgeTime v) =
      F.forest.graph.dist u v := by
  have hconn := (F.forest.isTree_of_one_root (one_root_of_terminal_valid hF) hF.acyclic).connected
  have he := graphIso_dist_eq (canonicalTreeIso hF ht ho) hconn ⟨u, hu⟩ ⟨v, hv⟩
  rw [forest_toGraph_dist_eq] at he
  have hvalid := ForwardHistory.state_valid x (canonicalHistory x n F)
  change Freezing1.Forward.ValidAt (canonicalHistory x n F).length
    (canonicalForwardState x n F) at hvalid
  rw [forward_tree_dist_eq hvalid] at he
  exact he

/-- Root distances use the source's distinguished root and forward identifier zero. -/
theorem canonicalForwardState_root_dist {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {r v : ℕ ⊕ ℕ} (hr : r ∈ F.forest.roots) (hv : v ∈ F.forest.vertices) :
    (canonicalForwardState x n F).graph.dist 0 (F.edgeTime v) = F.forest.graph.dist r v := by
  have hrV := (Freezing1.RootedForest.mem_roots.mp hr).1
  have hz := (ht.root_zero r hrV).mpr hr
  simpa only [hz] using canonicalForwardState_graph_dist hF ht ho hrV hv

end ReverseStamped
end Freezing2
