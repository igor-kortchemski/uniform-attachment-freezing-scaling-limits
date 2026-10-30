module

public import Freezing2.Companion.RootedForest

/-!
# Distances preserved by forest growth

Acyclic supergraphs cannot shorten an already existing path. When two rooted
components are joined, the path between old vertices in different components
consists of their two root paths and the new edge. These are deterministic
ingredients of the coalescence-time distance identity in Proposition `height=ok`.
-/

@[expose] public section

open SimpleGraph

namespace Freezing2

variable {V : Type*}

/-- Every path in an acyclic graph realizes graph distance. -/
theorem path_length_eq_dist_of_acyclic {G : SimpleGraph V} (hG : G.IsAcyclic)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q, hq, hlen⟩ := p.reachable.exists_path_of_dist
  have he := (hG.subsingleton_path u v).elim (⟨p, hp⟩ : G.Path u v) ⟨q, hq⟩
  have he' : p = q := congrArg Subtype.val he
  exact he' ▸ hlen

/-- Adding edges without creating cycles preserves every existing finite distance. -/
theorem dist_eq_of_acyclic_supergraph {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : H.IsAcyclic) {u v : V} (huv : G.Reachable u v) :
    H.dist u v = G.dist u v := by
  obtain ⟨p, hp, hlen⟩ := huv.exists_path_of_dist
  have h := path_length_eq_dist_of_acyclic hH (hp.mapLe hGH)
  rw [Walk.length_mapLe] at h
  exact h.symm.trans hlen

variable [DecidableEq V]

/-- Every vertex on a root path has the same component root. -/
theorem root_eq_on_root_path (F : Freezing1.RootedForest V) {v z : V}
    (hv : v ∈ F.vertices) (p : F.graph.Walk (F.root v) v) (hz : z ∈ p.support) :
    F.root z = F.root v := by
  have h := F.root_eq_of_walk (p.takeUntil z hz)
  rw [F.root_fixed v hv] at h
  exact h.symm

/-- Exact distance immediately after joining the two previously different components. -/
theorem join_cross_distance (F : Freezing1.RootedForest V) (hF : F.graph.IsAcyclic)
    {u v : V} (hu : u ∈ F.vertices) (hv : v ∈ F.vertices)
    (hne : F.root u ≠ F.root v) :
    (F.join (F.root u) (F.root v) (F.root_mem_roots hu) (F.root_mem_roots hv) hne).graph.dist u v =
      F.depth u + F.depth v + 1 := by
  let J := F.join (F.root u) (F.root v) (F.root_mem_roots hu) (F.root_mem_roots hv) hne
  have hJ : J.graph.IsAcyclic := F.join_isAcyclic hF _ _ _
  have hle : F.graph ≤ J.graph := by
    rw [Freezing1.RootedForest.join_graph]
    exact le_sup_left
  have hedge : J.graph.Adj (F.root u) (F.root v) := by
    rw [Freezing1.RootedForest.join_graph]
    exact Or.inr (by simp [SimpleGraph.edge_adj, hne])
  obtain ⟨pu, hpu⟩ := F.exists_root_walk hu
  obtain ⟨pv, hpv⟩ := F.exists_root_walk hv
  have hpuPath : pu.IsPath := pu.isPath_of_length_eq_dist (hpu.trans (F.depth_eq_dist hu))
  have hpvPath : pv.IsPath := pv.isPath_of_length_eq_dist (hpv.trans (F.depth_eq_dist hv))
  let P : J.graph.Walk u (F.root u) := pu.reverse.mapLe hle
  let Q : J.graph.Walk (F.root u) v := .cons hedge (pv.mapLe hle)
  have hPQ : (P.append Q).IsPath := by
    rw [Walk.isPath_append]
    refine ⟨hpuPath.reverse.mapLe hle, ?_, ?_⟩
    · simpa [Q] using hpvPath.mapLe hle
    · apply List.disjoint_left.mpr
      intro z hzu hzv
      have hzu' : z ∈ pu.support := by simpa [P] using hzu
      have hzv' : z ∈ pv.support := by simpa [Q] using hzv
      exact hne ((root_eq_on_root_path F hu pu hzu').symm.trans
        (root_eq_on_root_path F hv pv hzv'))
  have hlen := path_length_eq_dist_of_acyclic hJ hPQ
  rw [← hlen]
  simp [P, Q, hpu, hpv]
  omega

end Freezing2
